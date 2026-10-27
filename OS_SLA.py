"""resource_allocation_simulator.py - Resource Allocation Simulator (single file).
Classical Banker's Algorithm vs DBDAA (Dynamic Banker's Deadlock Avoidance
Algorithm, Zohora, Farhin and Kaiser, PLOS ONE 19(9), e0310807, 2024).
Run:  python resource_allocation_simulator.py        (needs only Python + Tkinter)
Event format, one per line in the Events box:
    pid v1 v2 ...      a request by process pid        e.g.  1 1 0 2
    NEW m1 m2 ...      a new process arrives at run time with that Max
                       (DBDAA accepts it; classical Banker's cannot, set is fixed)
"""
import time
import tkinter as tk
from dataclasses import dataclass, field
from tkinter import ttk, messagebox
from typing import List, Optional
# ============================================================================
# 1. Data structures
# ============================================================================
@dataclass
class SystemState:
    total: List[int]
    maximum: List[List[int]]
    allocation: List[List[int]]
    @property
    def n(self) -> int:
        return len(self.maximum)
    @property
    def m(self) -> int:
        return len(self.total)
    def need(self):
        return [[self.maximum[i][j] - self.allocation[i][j] for j in range(self.m)]
                for i in range(self.n)]
    def available(self):
        return [self.total[j] - sum(self.allocation[i][j] for i in range(self.n))
                for j in range(self.m)]
    def copy(self):
        return SystemState(self.total[:], [r[:] for r in self.maximum],
                           [r[:] for r in self.allocation])
@dataclass
class Request:
    pid: int
    amount: List[int]
@dataclass
class NewProcess:
    maximum: List[int]
    allocation: Optional[List[int]] = None
@dataclass
class Deferred:
    pid: int
    amount: List[int]
    step: int
@dataclass
class RunResult:
    algorithm: str
    log: List[str] = field(default_factory=list)
    granted: int = 0
    denied: int = 0
    deferred: int = 0
    retried_granted: int = 0
    completed: List[int] = field(default_factory=list)
    still_deferred: List[int] = field(default_factory=list)
    operations: int = 0
    time_us: float = 0.0
    avg_utilization: float = 0.0
    final_available: List[int] = field(default_factory=list)
    dynamic_support: bool = False
# ============================================================================
# 2. Input parsing and validation
# ============================================================================
def parse_vector(text, expected_len=None, name="vector"):
    parts = text.replace(",", " ").split()
    if not parts:
        raise ValueError(f"{name} is empty.")
    try:
        vec = [int(p) for p in parts]
    except ValueError:
        raise ValueError(f"{name} must contain only whole numbers.")
    if any(v < 0 for v in vec):
        raise ValueError(f"{name} cannot contain negative numbers.")
    if expected_len is not None and len(vec) != expected_len:
        raise ValueError(f"{name} needs {expected_len} values, got {len(vec)}.")
    return vec
def validate_state(state: SystemState):
    if state.n == 0 or state.m == 0:
        raise ValueError("At least 1 process and 1 resource type are required.")
    if state.n > 20 or state.m > 10:
        raise ValueError("Limit exceeded: max 20 processes and 10 resource types.")
    if len(state.allocation) != state.n:
        raise ValueError("Max and Allocation need the same number of rows.")
    for i in range(state.n):
        for j in range(state.m):
            if state.allocation[i][j] > state.maximum[i][j]:
                raise ValueError(f"Allocation exceeds Max for P{i}, resource R{j}.")
            if state.maximum[i][j] > state.total[j]:
                raise ValueError(f"Max of P{i} for R{j} exceeds total instances.")
    if any(a < 0 for a in state.available()):
        raise ValueError("Allocated resources exceed the total available in the system.")
def validate_request(state: SystemState, req: Request):
    if not 0 <= req.pid < state.n:
        raise ValueError(f"Process id P{req.pid} does not exist (valid: P0-P{state.n
- 1}).")
    if len(req.amount) != state.m:
        raise ValueError(f"Request must have {state.m} values.")
def parse_events(text, m):
    events = []
    for ln, line in enumerate(text.strip().splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if line.upper().startswith("NEW"):
            events.append(NewProcess(parse_vector(line[3:], m, f"Events line {ln}(NEW)")))
        else:
            v = parse_vector(line, m + 1, f"Events line {ln}")
            events.append(Request(v[0], v[1:]))
    return events
def seq_text(seq):
    return ", ".join(f"P{p}" for p in seq)
# ============================================================================
# 3. Classical Banker's Algorithm (static process set)
# ============================================================================
def is_safe(state, counter):
    need, work = state.need(), state.available()
    finish, seq, progress = [False] * state.n, [], True
    while progress:
        progress = False
        for i in range(state.n):
            if finish[i]:
                continue
            counter[0] += state.m
            if all(need[i][j] <= work[j] for j in range(state.m)):
                work = [work[j] + state.allocation[i][j] for j in range(state.m)]
                finish[i] = True
                seq.append(i)
                progress = True
    return all(finish), seq
def release_finished_classic(state, result):
    for i in range(state.n):
        if i not in result.completed and any(state.maximum[i]) \
                and state.allocation[i] == state.maximum[i]:
            state.allocation[i] = [0] * state.m
            result.completed.append(i)
            result.log.append(f"  P{i} finished and released its resources.")
def run_bankers(initial, events):
    state, result = initial.copy(), RunResult("Classical Banker's Algorithm")
    counter, util = [0], []
    start = time.perf_counter()
    ok, seq = is_safe(state, counter)
    result.log.append(f"Initial state is {'SAFE' if ok else 'UNSAFE'}"
                      + (f": <{seq_text(seq)}>" if ok else ""))
    for step, ev in enumerate(events, 1):
        if isinstance(ev, NewProcess):
            result.denied += 1
            result.log.append(f"Step {step}: NEW process Max {ev.maximum} -> IGNORED
"
                              "(classical Banker's needs a fixed process set)")
        else:
            validate_request(state, ev)
            need, avail = state.need()[ev.pid], state.available()
            tag = f"Step {step}: P{ev.pid} requests {ev.amount}"
            counter[0] += 2 * state.m
            if any(ev.amount[j] > need[j] for j in range(state.m)):
                result.denied += 1
                result.log.append(f"{tag} -> DENIED (exceeds declared maximum
claim)")
            elif any(ev.amount[j] > avail[j] for j in range(state.m)):
                result.denied += 1
                result.log.append(f"{tag} -> DENIED (not enough resources, must
wait)")
            else:
                trial = state.copy()
                for j in range(state.m):
                    trial.allocation[ev.pid][j] += ev.amount[j]
                safe, seq = is_safe(trial, counter)
                if safe:
                    state = trial
                    result.granted += 1
                    result.log.append(f"{tag} -> GRANTED (safe: <{seq_text(seq)}>)")
                    release_finished_classic(state, result)
                else:
                    result.denied += 1
                    result.log.append(f"{tag} -> DENIED (would lead to UNSAFE
state)")
        util.append(100.0 * sum(sum(r) for r in state.allocation) / max(1,
sum(state.total)))
    result.time_us = (time.perf_counter() - start) * 1e6
    result.operations = counter[0]
    result.avg_utilization = sum(util) / len(util) if util else 0.0
    result.final_available = state.available()
    return result
# ============================================================================
# 4. DBDAA (Dynamic Banker's Deadlock Avoidance Algorithm)
#    Max_Need sorting + Min_A safety test + Primary Unsafe list + timer cycles
# ============================================================================
def max_need(row):
    return max(row) if row else 0
def sorted_queue(state, done=()):
    need = state.need()
    return sorted((i for i in range(state.n) if i not in done),
                  key=lambda i: (max_need(need[i]), i))
def is_safe_dbdaa(state, counter, done=()):
    m = state.m
    need, work = state.need(), state.available()
    order = sorted_queue(state, done)
    finish = {i: False for i in order}
    seq = []
    min_a = min(work)
    counter[0] += m - 1
    progress = True
    while progress:
        progress = False
        for i in order:
            if finish[i]:
                continue
            counter[0] += 1                         # Max_Need[i] <= Min_A ?
            if max_need(need[i]) <= min_a:          # fast path: one comparison
                fits = True
            else:
                counter[0] += m                     # fallback: vector comparison
                fits = all(need[i][j] <= work[j] for j in range(m))
            if fits:
                work = [work[j] + state.allocation[i][j] for j in range(m)]
                finish[i] = True
                seq.append(i)
                progress = True
                min_a = min(work)
                counter[0] += m - 1
    return all(finish.values()), seq
def evaluate(state, req, counter, done):
    """Returns (verdict, new_state, seq, reason); verdict GRANT / DEFER / REJECT."""
    m = state.m
    need, avail = state.need()[req.pid], state.available()
    counter[0] += 2 * m
    if req.pid in done:
        return "REJECT", None, [], "process already finished"
    if any(req.amount[j] > need[j] for j in range(m)):
        return "REJECT", None, [], "exceeds declared maximum claim"
    if any(req.amount[j] > avail[j] for j in range(m)):
        return "DEFER", None, [], "not enough free resources"
    trial = state.copy()                            # pretend to allocate
    for j in range(m):
        trial.allocation[req.pid][j] += req.amount[j]
    safe, seq = is_safe_dbdaa(trial, counter, done)
    if safe:
        return "GRANT", trial, seq, "safe"
    return "DEFER", None, seq, "would lead to UNSAFE state"
def release_finished(state, result, done):
    for i in range(state.n):
        if i not in done and any(state.maximum[i]) and state.allocation[i] ==
state.maximum[i]:
            state.allocation[i] = [0] * state.m
            done.add(i)
            result.completed.append(i)
            result.log.append(f"  P{i} finished and released its resources.")
def admit(state, ev, counter, done, result, tag):
    m, pid = state.m, state.n
    alloc = list(ev.allocation) if ev.allocation is not None else [0] * m
    counter[0] += m
    if any(ev.maximum[j] > state.total[j] for j in range(m)):       # early rejection
        result.denied += 1
        result.log.append(f"{tag}: NEW process Max {ev.maximum} -> EARLY REJECT (Max
exceeds Total)")
        return state
    trial = state.copy()
    trial.maximum.append(list(ev.maximum))
    trial.allocation.append(alloc)
    safe, seq = is_safe_dbdaa(trial, counter, done)
    if not safe:
        result.denied += 1
        result.log.append(f"{tag}: NEW process Max {ev.maximum} -> REJECTED (would
make state UNSAFE)")
        return state
    result.log.append(f"{tag}: NEW process P{pid} Max {ev.maximum} joins the ready
queue "
                      f"-> SAFE: <{seq_text(seq)}>")
    return trial
def timer_cycle(state, deferred, counter, done, result, max_cycles=10):
    cycles, changed = 0, True
    while changed and deferred and cycles < max_cycles:
        changed = False
        cycles += 1
        need = state.need()
        for item in sorted(deferred, key=lambda d: (max_need(need[d.pid]), d.pid)):
            verdict, trial, seq, why = evaluate(state, Request(item.pid,
item.amount), counter, done)
            tag = f"  [timer {cycles}] retry P{item.pid} {item.amount}"
            if verdict == "GRANT":
                state = trial
                deferred.remove(item)
                result.granted += 1
                result.retried_granted += 1
                result.log.append(f"{tag} -> GRANTED (safe: <{seq_text(seq)}>)")
                release_finished(state, result, done)
                changed = True
                break
            if verdict == "REJECT":
                deferred.remove(item)
                result.denied += 1
                result.log.append(f"{tag} -> REJECTED ({why})")
                changed = True
                break
    return state
def run_dbdaa(initial, events):
    state, result = initial.copy(), RunResult("DBDAA (Dynamic Banker's)")
    result.dynamic_support = True
    counter, util, deferred, done = [0], [], [], set()
    start = time.perf_counter()
    ok, seq = is_safe_dbdaa(state, counter, done)
    need = state.need()
    queue = ", ".join(f"P{i}({max_need(need[i])})" for i in sorted_queue(state))
    result.log.append(f"Queue sorted by Max_Need: [{queue}]")
    result.log.append(f"Initial state is {'SAFE' if ok else 'UNSAFE'}"
                      + (f": <{seq_text(seq)}>" if ok else ""))
    for step, ev in enumerate(events, 1):
        if isinstance(ev, NewProcess):
            state = admit(state, ev, counter, done, result, f"Step {step}")
        else:
            validate_request(state, ev)
            tag = f"Step {step}: P{ev.pid} requests {ev.amount}"
            if any(d.pid == ev.pid for d in deferred):
                result.denied += 1
                result.log.append(f"{tag} -> IGNORED (P{ev.pid} is already on the
Primary Unsafe list)")
            else:
                verdict, trial, seq, why = evaluate(state, ev, counter, done)
                if verdict == "GRANT":
                    state = trial
                    result.granted += 1
                    result.log.append(f"{tag} -> GRANTED (safe: <{seq_text(seq)}>)")
                    release_finished(state, result, done)
                elif verdict == "REJECT":
                    result.denied += 1
                    result.log.append(f"{tag} -> REJECTED ({why})")
                else:
                    deferred.append(Deferred(ev.pid, list(ev.amount), step))
                    result.deferred += 1
                    result.log.append(f"{tag} -> DEFERRED to Primary Unsafe list
({why})")
        state = timer_cycle(state, deferred, counter, done, result)
        util.append(100.0 * sum(sum(r) for r in state.allocation) / max(1,
sum(state.total)))
    result.still_deferred = [d.pid for d in deferred]
    if deferred:
        result.log.append("Still on Primary Unsafe list: "
                          + ", ".join(f"P{d.pid} {d.amount}" for d in deferred))
    result.time_us = (time.perf_counter() - start) * 1e6
    result.operations = counter[0]
    result.avg_utilization = sum(util) / len(util) if util else 0.0
    result.final_available = state.available()
    return result
# ============================================================================
# 5. Tkinter GUI
# ============================================================================
SAMPLES = {
    "Classic (5P, 3R)": dict(
        total="10 5 7",
        maxm="7 5 3\n3 2 2\n9 0 2\n2 2 2\n4 3 3",
        alloc="0 1 0\n2 0 0\n3 0 2\n2 1 1\n0 0 2",
        events="1 1 0 2\n4 3 3 0\n0 0 2 0"),
    "Deadlock-prone (2P, 2R)": dict(
        total="1 1", maxm="1 1\n1 1", alloc="0 0\n0 0",
        events="0 1 0\n1 0 1\n0 0 1\n1 1 0"),
    "Classic + new process at runtime": dict(
        total="10 5 7",
        maxm="7 5 3\n3 2 2\n9 0 2\n2 2 2\n4 3 3",
        alloc="0 1 0\n2 0 0\n3 0 2\n2 1 1\n0 0 2",
        events="1 1 0 2\nNEW 2 2 2\n4 3 3 0\n0 0 2 0"),
}
BG, DARK, ACCENT, ACCENT2 = "#EEF3F4", "#0F2A33", "#0E7C86", "#F5A524"
class SimulatorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Resource Allocation Simulator - Classical Banker's vs DBDAA")
        self.geometry("1050x760")
        self.configure(bg=BG)
        self._style()
        self._header()
        self._input_panel()
        self._control_panel()
        self._output_panel()
        self.load_sample("Classic (5P, 3R)")
    # ---------- layout ----------
    def _style(self):
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("TFrame", background=BG)
        st.configure("TLabelframe", background=BG)
        st.configure("TLabelframe.Label", background=BG, foreground=DARK, font=
("Segoe UI", 10, "bold"))
        st.configure("TLabel", background=BG, foreground=DARK)
        st.configure("TRadiobutton", background=BG, foreground=DARK)
        st.configure("Run.TButton", background=ACCENT, foreground="white", font=
("Segoe UI", 10, "bold"))
        st.map("Run.TButton", background=[("active", "#0B636B")])
        st.configure("Treeview.Heading", font=("Segoe UI", 10, "bold"))
        st.configure("Treeview", rowheight=26)
    def _header(self):
        h = tk.Frame(self, bg=DARK)
        h.pack(fill="x")
        tk.Label(h, text="Resource Allocation Simulator", bg=DARK, fg="white",
                 font=("Segoe UI", 16, "bold")).pack(side="left", padx=14, pady=8)
        tk.Label(h, text="Classical Banker's vs DBDAA (Dynamic Mode)", bg=DARK,
fg=ACCENT2,
                 font=("Segoe UI", 10)).pack(side="left", padx=4)
    def _text(self, parent, label, row, height, col=0):
        ttk.Label(parent, text=label).grid(row=row, column=col, sticky="nw", padx=4,
pady=3)
        t = tk.Text(parent, width=30, height=height, font=("Courier New", 10),
relief="solid", bd=1)
        t.grid(row=row, column=col + 1, sticky="w", padx=4, pady=3)
        return t
    def _input_panel(self):
        f = ttk.LabelFrame(self, text="1. System input")
        f.pack(fill="x", padx=10, pady=(8, 4))
        ttk.Label(f, text="Load sample:").grid(row=0, column=0, sticky="w", padx=4,
pady=3)
        self.sample_var = tk.StringVar(value="Classic (5P, 3R)")
        cb = ttk.Combobox(f, textvariable=self.sample_var, values=list(SAMPLES),
                          state="readonly", width=34)
        cb.grid(row=0, column=1, sticky="w", padx=4)
        cb.bind("<<ComboboxSelected>>", lambda e:
self.load_sample(self.sample_var.get()))
        ttk.Label(f, text="Total resources:").grid(row=1, column=0, sticky="w",
padx=4, pady=3)
        self.total_e = ttk.Entry(f, width=32, font=("Courier New", 10))
        self.total_e.grid(row=1, column=1, sticky="w", padx=4)
        self.max_t = self._text(f, "Max matrix\n(row per process):", 2, 5)
        self.alloc_t = self._text(f, "Allocation matrix:", 2, 5, col=2)
        self.ev_t = self._text(f, "Events (one per line):", 1, 4, col=2)
        ttk.Label(f, text="pid v1 v2 ... = request     NEW m1 m2 ... = new process at
runtime",
                  foreground="#3D5A66").grid(row=0, column=2, columnspan=2,
sticky="w", padx=4)
    def _control_panel(self):
        f = ttk.LabelFrame(self, text="2. Select algorithm and run")
        f.pack(fill="x", padx=10, pady=4)
        self.algo = tk.StringVar(value="both")
        for text, val in [("Classical Banker's", "classic"), ("DBDAA (Dynamic)",
"dbdaa"),
                          ("Compare both", "both")]:
            ttk.Radiobutton(f, text=text, variable=self.algo,
value=val).pack(side="left", padx=10, pady=6)
        ttk.Button(f, text="Run Simulation", style="Run.TButton",
command=self.run).pack(side="left", padx=14)
        ttk.Button(f, text="Clear Output", command=self.clear).pack(side="left")
    def _output_panel(self):
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=10, pady=(4, 10))
        self.log_t = tk.Text(self.nb, state="disabled", font=("Courier New", 10),
                             bg="#0F2A33", fg="#E6F2F3", relief="flat", padx=8,
pady=8)
        self.log_t.tag_configure("title", foreground="#F5A524", font=("Courier New",
10, "bold"))
        self.log_t.tag_configure("ok", foreground="#7FE3C0")
        self.log_t.tag_configure("bad", foreground="#FF8A75")
        self.log_t.tag_configure("wait", foreground="#F5C66B")
        self.nb.add(self.log_t, text="3. Execution log")
        cmp_f = ttk.Frame(self.nb)
        self.nb.add(cmp_f, text="4. Performance comparison")
        cols = ("Metric", "Classical Banker's", "DBDAA (Dynamic)")
        self.tree = ttk.Treeview(cmp_f, columns=cols, show="headings", height=11)
        for c, w in zip(cols, (260, 260, 260)):
            self.tree.heading(c, text=c)
            self.tree.column(c, width=w, anchor="w")
        self.tree.pack(fill="x", padx=8, pady=8)
        self.verdict = ttk.Label(cmp_f, text="", font=("Segoe UI", 10, "bold"),
wraplength=900)
        self.verdict.pack(anchor="w", padx=10)
    # ---------- actions ----------
    @staticmethod
    def _set(widget, text):
        if isinstance(widget, tk.Text):
            widget.delete("1.0", "end")
            widget.insert("1.0", text)
        else:
            widget.delete(0, "end")
            widget.insert(0, text)
    def load_sample(self, name):
        s = SAMPLES[name]
        self._set(self.total_e, s["total"])
        self._set(self.max_t, s["maxm"])
        self._set(self.alloc_t, s["alloc"])
        self._set(self.ev_t, s["events"])
        self.clear()
    def _read_input(self):
        total = parse_vector(self.total_e.get(), name="Total resources")
        m = len(total)
        def grid(widget, nm):
            lines = [l for l in widget.get("1.0", "end").strip().splitlines() if
l.strip()]
            return [parse_vector(l, m, f"{nm} row {i}") for i, l in enumerate(lines)]
        state = SystemState(total, grid(self.max_t, "Max"), grid(self.alloc_t,
"Allocation"))
        validate_state(state)
        events = parse_events(self.ev_t.get("1.0", "end"), m)
        return state, events
    def run(self):
        try:
            state, events = self._read_input()
            choice, res = self.algo.get(), {}
            if choice in ("classic", "both"):
                res["c"] = run_bankers(state, events)
            if choice in ("dbdaa", "both"):
                res["d"] = run_dbdaa(state, events)
        except ValueError as e:
            messagebox.showerror("Invalid input", str(e))
            return
        self.clear()
        self.log_t.config(state="normal")
        for r in res.values():
            self.log_t.insert("end", f"=== {r.algorithm} ===\n", "title")
            for line in r.log:
                tag = ("ok" if "GRANTED" in line or "joins" in line else
                       "wait" if "DEFERRED" in line or "still" in line else
                       "bad" if any(w in line for w in ("DENIED", "REJECT",
"IGNORED")) else None)
                self.log_t.insert("end", line + "\n", tag)
            self.log_t.insert("end", "\n")
        self.log_t.config(state="disabled")
        self._fill_table(res.get("c"), res.get("d"))
        if choice == "both":
            self.nb.select(1)
    def _fill_table(self, c, d):
        def val(r, f):
            if r is None:
                return "-"
            v = getattr(r, f)
            if f in ("completed", "still_deferred"):
                return ", ".join(f"P{p}" for p in v) if v else "none"
            if f == "dynamic_support":
                return "Yes (runtime arrival)" if v else "No (fixed process set)"
            if isinstance(v, float):
                return f"{v:.1f}"
            return str(v)
        rows = [("Requests granted", "granted"), ("Denied / rejected", "denied"),
                ("Deferred (Primary Unsafe list)", "deferred"),
                ("Deferred requests granted later", "retried_granted"),
                ("Still deferred at end", "still_deferred"),
                ("Processes completed", "completed"),
                ("Operations (comparisons)", "operations"), ("Time (us)", "time_us"),
                ("Average utilization (%)", "avg_utilization"),
                ("Final available", "final_available"),
                ("Dynamic process arrival", "dynamic_support")]
        for label, f in rows:
            self.tree.insert("", "end", values=(label, val(c, f), val(d, f)))
        if c and d:
            self.verdict.config(text=(
                f"Operations: classical {c.operations} vs DBDAA {d.operations}. "
                "DBDAA accepts runtime arrivals and retries deferred requests."))
    def clear(self):
        self.log_t.config(state="normal")
        self.log_t.delete("1.0", "end")
        self.log_t.config(state="disabled")
        self.tree.delete(*self.tree.get_children())
        self.verdict.config(text="")
if __name__ == "__main__":
    SimulatorApp().mainloop()