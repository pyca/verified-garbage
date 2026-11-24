module

public import VerifiedGarbage.Proof.Ffdh.X86.QPower
public import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.QPower
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
meta import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
meta import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets

/-!
# FFDH on i686: the traces of a power to q

The power to q runs over q's bytes from its first nonzero one, so its trace
depends on where that byte is. The domain is public: runs from states with
the same bytes of q (`QRun`, for a `bs` that fixes them) scan the same
bytes, which is the one piece the taint analysis cannot check, since it
branches on what it reads (`qScan_trace`: byte by byte, each run before the
same byte, the branch on `lead` of the same bytes). The callee's arguments
10 and 11, which `setQ` writes from the scan's words, are then the same in
both runs, and the load and the windowed power are checked from them as
from any public arguments (`winQCall_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.QPower

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86 VG.Proof.Ffdh
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86

/-! ## The taint checks -/

theorem qScanInit_check : ACheck (.block qScanInit) := by dsimp only [ACheck]; taint_decide
theorem qScanStep_check : (VG.Taint.check taint τAs (.block qScanStep) (.block [])).isSome = true := by
  taint_decide
theorem qScanEnd_check : ACheck (.block qScanEnd) := by dsimp only [ACheck]; taint_decide
theorem setQ_check : (VG.Taint.check taint (τr [.esp, .edi]) (.block setQ) (.block [])).isSome = true := by
  taint_decide
theorem loadTopQ_check : ACheck (loadTop (.slot .wide 8) (one .wide) 10 11) := by
  dsimp only [ACheck]; taint_decide

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {bs : List Byte}

/-- A run before a power to q: the domain with q's bytes `bs`, apart from what a stage changes. -/
structure QRun (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (bs : List Byte) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  room : RoomF sp base bytes
  geo : DomGeo args base bytes len (3 * len) u.rd u.wr
  hb40 : Region.Disjoint ⟨byteAddr (args 2), 3 * len⟩ (below sp 176)
  q : qBytes u.mem args len = bs

theorem QRun.step {u v : State} (A : QRun Ex base bytes len args sp bs u)
    (S : Step Ex base bytes len args u v) : QRun Ex base bytes len args sp bs v :=
  ⟨run_step A.run S, A.room, A.geo.keep ⟨rfl, rfl⟩ S.keeps, A.hb40,
    (qBytes_keep A.run.1 A.geo (by rw [A.run.2.2]; exact A.room) (by rw [A.run.2.2]; exact A.hb40) S.frame).trans
      A.q⟩

/-- A run with the domain `D` of three components: its q is `D`'s third. -/
theorem QRun.of_dom {D : List Byte} {u : State} (run : Run Ex base bytes len args sp u)
    (room : RoomF sp base bytes) (geo : DomGeo args base bytes len (3 * len) u.rd u.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), 3 * len⟩ (below sp 176))
    (dom : Spec.Rsa.bytesAt u.mem (byteAddr (args 2)) (3 * len) = D) :
    QRun Ex base bytes len args sp ((D.drop (2 * len)).take len) u :=
  ⟨run, room, geo, hb40, by
    rw [← dom]
    exact (VG.Proof.Dsa.bytesAt_slice u.mem _ (total := 3 * len) (offset := 2 * len) (len := len)
      (by omega_arith)).symm⟩

/-! ## The scan -/

/-- The scan before byte `i`, from a run with q's bytes `bs`. -/
def SQ (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (bs : List Byte) (i : Nat) (u : State) : Prop :=
  ∃ s, QRun Ex base bytes len args sp bs s ∧ ScanAt s len i args u

theorem SQ.run {i : Nat} {u : State} (h : SQ Ex base bytes len args sp bs i u) :
    Run Ex base bytes len args sp u :=
  let ⟨_, A, I⟩ := h
  ⟨A.run.1.regs I.keeps I.mem, A.run.2.1.keep I.keeps, (I.keeps.1 _ (by decide)).trans A.run.2.2⟩

/-- Before the same byte, the runs' pointers into q are the same. -/
theorem SQ.agreeS {i : Nat} {u₁ u₂ : State} (h₁ : SQ Ex base bytes len args sp bs i u₁)
    (h₂ : SQ Ex base bytes len args sp bs i u₂) : VG.X86.Taint.Agree τAs u₁ u₂ := by
  obtain R₁ := h₁.run
  obtain R₂ := h₂.run
  obtain ⟨_, _, I₁⟩ := h₁
  obtain ⟨_, _, I₂⟩ := h₂
  exact agreeAs R₁.1 R₂.1 R₁.2.1 R₂.2.1 (R₁.2.2.trans R₂.2.2.symm) (I₁.esi.trans I₂.esi.symm)

/-- After byte `i`: before the next one, or still at `lead`, which ZF tells. -/
abbrev SQz (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (bs : List Byte) (i : Nat) (v : State) : Prop :=
  SQ Ex base bytes len args sp bs (if i < lead bs then i + 1 else i) v ∧
    v.zf = some (decide (¬ i < lead bs))

/-- The scan's runs over the same bytes leak the same traces: each byte is read at the same address, and
the loop ends at `lead` of the bytes in both. -/
theorem qScan_trace : RelCT isa (Both (QRun Ex base bytes len args sp bs)) qScan fun _ _ => True := by
  unfold qScan
  refine VG.RelCT.seq (R := fun a b => ∃ i, lead bs = lead bs - i ∧ i ≤ lead bs ∧
      SQ Ex base bytes len args sp bs i a ∧ SQ Ex base bytes len args sp bs i b) ?_ ?_
  · exact ((RelCT.taint (A := taint) τA (fun _ _ h => h.1.run.agree h.2.run) qScanInit_check).wp
      (F₁ := SQ Ex base bytes len args sp bs 0) (F₂ := SQ Ex base bytes len args sp bs 0)
      fun a b h => ⟨WP.mono (qScanInit_ok h.1.run.1 h.1.geo) fun _ I => ⟨a, h.1, I⟩,
        WP.mono (qScanInit_ok h.2.run.1 h.2.geo) fun _ I => ⟨b, h.2, I⟩⟩).mono (fun _ _ h => h)
      fun _ _ h => ⟨0, rfl, Nat.zero_le _, h.2.1, h.2.2⟩
  refine VG.RelCT.seq (R := Both (SQ Ex base bytes len args sp bs (lead bs)))
    (RelCT.loop (M := isa) (fun n (a b : State) => ∃ i, n = lead bs - i ∧ i ≤ lead bs ∧
      SQ Ex base bytes len args sp bs i a ∧ SQ Ex base bytes len args sp bs i b) (fun n => ?_) (lead bs))
    (RelCT.taint (A := taint) τA (fun _ _ h => h.1.run.agree h.2.run) qScanEnd_check)
  refine RelCT.exists_ (M := isa) (P := fun i (a b : State) => n = lead bs - i ∧ i ≤ lead bs ∧
      SQ Ex base bytes len args sp bs i a ∧ SQ Ex base bytes len args sp bs i b) fun i => ?_
  by_cases hn : n = lead bs - i ∧ i ≤ lead bs
  swap
  · exact RelCT.of_false fun _ _ h => hn ⟨h.1, h.2.1⟩
  obtain ⟨hn, hi⟩ := hn
  have w : ∀ a, SQ Ex base bytes len args sp bs i a →
      WP isa (.block qScanStep) a (SQz Ex base bytes len args sp bs i) := fun a ⟨s, A, I⟩ =>
    WP.mono (qScanStep_ok A.geo (by rw [A.q]; exact hi) I) fun v ⟨Iv, z⟩ =>
      ⟨⟨s, A, by rw [A.q] at Iv; exact Iv⟩, by rw [A.q] at z; exact z⟩
  have ev : ∀ v : State, v.zf = some (decide (¬ i < lead bs)) →
      isa.eval .ne v = some (!decide (¬ i < lead bs)) := fun v z => by
    show v.zf.map (!·) = _
    rw [z]; rfl
  refine ((RelCT.taint (A := taint) τAs (fun _ _ h => h.2.2.1.agreeS h.2.2.2) qScanStep_check).wp
    (F₁ := SQz Ex base bytes len args sp bs i) (F₂ := SQz Ex base bytes len args sp bs i)
    fun a b h => ⟨w a h.2.2.1, w b h.2.2.2⟩).mono (fun _ _ h => h) fun x y h => ?_
  obtain ⟨-, ⟨Sx, zx⟩, ⟨Sy, zy⟩⟩ := h
  refine ⟨(ev x zx).trans (ev y zy).symm, fun e => ?_, fun e => ?_⟩
  · rw [ev x zx] at e
    obtain nl : ¬ i < lead bs := by simpa using e
    rw [ite_eq_right nl] at Sx Sy
    obtain rfl : i = lead bs := by omega_arith
    exact ⟨Sx, Sy⟩
  · rw [ev x zx] at e
    obtain il : i < lead bs := by simpa using e
    rw [ite_eq_left il] at Sx Sy
    exact ⟨lead bs - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, Sx, Sy⟩

/-- The scan, with what each run reaches: its two words. -/
theorem qScan_relCT : RelCT isa (Both (QRun Ex base bytes len args sp bs)) qScan
    (Both fun u => QRun Ex base bytes len args sp bs u ∧ QAt base len args bs u.mem) :=
  relCT_both qScan_trace fun _ A => WP.mono (qScan_ok A.run.1 A.geo) fun _ ⟨S, Q, _⟩ =>
    ⟨A.step S, by rw [A.q] at Q; exact Q⟩

/-! ## The power -/

/-- A fact each run keeps by its own correctness, through code whose runs leak the same traces. -/
theorem relCT_keep {P Q X : State → Prop} {c : Prog isa} (h : RelCT isa (Both P) c (Both Q))
    (hw : ∀ s, P s → X s → WP isa c s X) :
    RelCT isa (Both fun u => P u ∧ X u) c (Both fun u => Q u ∧ X u) :=
  ((h.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h).wp (F₁ := X) (F₂ := X)
    fun a b h => ⟨hw a h.1.1 h.1.2, hw b h.2.1 h.2.2⟩).mono (fun _ _ h => h)
    fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

/-- Before `winQCall`: a prepared context, and the scan's words for q's bytes `bs`. -/
abbrev QPre (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (bs : List Byte) (u : State) : Prop :=
  WinPre Ex base bytes len args sp u ∧ QRun Ex base bytes len args sp bs u ∧ QAt base len args bs u.mem

/-- The callee's state after the copy of the arguments, from a run of `P`, with its frame. -/
def CalleeW (P : State → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32)
    (u : State) : Prop :=
  ∃ s, P s ∧ CalleeAt base bytes len args sp u ∧ Frame (frameF base sp []) s.mem u.mem ∧ CalleeIn s u ∧
    s.gpr .esp = sp

/-- The callee's state after `setQ`, for its arguments `A`: it may read what the caller may. -/
def CalleeQ (P : State → Prop) (base : Addr) (bytes len : Nat) (A : Nat → BitVec 32) (sp : BitVec 32)
    (v : State) : Prop :=
  ∃ s, P s ∧ CalleeAt base bytes len A sp v ∧ Frame (frameF base sp []) s.mem v.mem ∧
    ∀ r ∈ s.rd ++ s.wr, r ∈ v.rd ++ v.wr

/-- `winQCall`: the copy of the arguments checked by the taint analysis from `esp`, `setQ` from `esp` and
`edi`, after which both callees have the same arguments (the scan's words, of the same bytes), and the
load and the windowed power related on the callees' states narrowed to the working space. -/
theorem winQCall_trace :
    RelCT isa (Both (QPre Ex base bytes len args sp bs)) winQCall fun _ _ => True := by
  suffices key : lead bs < len → len ≤ 1024 →
      RelCT isa (Both (QPre Ex base bytes len args sp bs)) winQCall fun _ _ => True from
    fun _ _ _ _ _ _ hp e₁ e₂ => key (qTail hp.1.2.1.geo hp.1.2.1.q
      (A := qArgs args (args 6 + BitVec.ofNat 32 (lead bs)) 0) rfl).1 hp.1.2.1.geo.upper _ _ _ _ _ _ hp e₁ e₂
  intro hl up
  obtain lb := len_le_bc len
  generalize hA : qArgs args (args 6 + BitVec.ofNat 32 (lead bs)) (BitVec.ofNat 32 (len - lead bs)) = A
  obtain e10 : A 10 = args 6 + BitVec.ofNat 32 (lead bs) := by rw [← hA]; rfl
  obtain e11 : A 11 = BitVec.ofNat 32 (len - lead bs) := by rw [← hA]; rfl
  have hP : ∀ s, QPre Ex base bytes len args sp bs s → Run Ex base bytes len args sp s ∧ RoomF sp base bytes :=
    fun _ W => ⟨W.1.1.1.run, W.1.1.2⟩
  -- `setQ`, from the callee's state.
  have wq : ∀ u, CalleeW (QPre Ex base bytes len args sp bs) base bytes len args sp u →
      WP isa (.block setQ) u (CalleeQ (QPre Ex base bytes len args sp bs) base bytes len A sp) :=
    fun u ⟨s, Ps, C, Fs, CI, e⟩ => by
      obtain ⟨R, RF⟩ := hP s Ps
      rw [← e] at RF Fs
      refine WP.mono (setQ_ok R.1 RF C.1 CI) fun v ⟨Kv, Fv, hv⟩ => ?_
      rw [frameF_word R.1 RF Fs (d := qpOff) (by decide), Ps.2.2.ptr,
        frameF_word R.1 RF Fs (d := qlOff) (by decide), Ps.2.2.cnt, hA] at hv
      obtain vesp : v.gpr .esp = u.gpr .esp := Kv.1 _ (by decide)
      refine ⟨s, Ps, ⟨hv, vesp.trans C.2.1, by rw [vesp]; exact C.2.2⟩, ?_, fun r hr => ?_⟩
      · rw [← e]
        exact Fs.trans (frameF_of_sub Fv fun r hr => by rw [List.mem_singleton.mp hr]; exact CI.sub)
      · rw [Kv.2.1, Kv.2.2, CI.rd, CI.wr]
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  -- The callee past `setQ`, narrowed to the working space.
  have nar : ∀ v, CalleeQ (QPre Ex base bytes len args sp bs) base bytes len A sp v →
      (WSt (fun _ _ => True) base bytes len A (sp - BitVec.ofNat 32 80) .wide [3, 4] 0
          (v.withRegions (v.rd ++ v.wr) [⟨base, bytes⟩]) ∧
        InRegions ((v.rd ++ v.wr) ++ [⟨base, bytes⟩]) (byteAddr (A 10)) (len - lead bs) ∧
        (A 10).toNat + (len - lead bs) ≤ 2 ^ 32 ∧
        Region.Disjoint ⟨byteAddr (A 10), len - lead bs⟩ ⟨base, bytes⟩) ∧
      ∃ F, WP isa (.seq (loadTop (.slot .wide 8) (one .wide) 10 11) (windowPowerWith .wide (lenCount 11)))
        (v.withRegions (v.rd ++ v.wr) [⟨base, bytes⟩]) F :=
    fun v ⟨s, Ps, C, Fs, hrd⟩ => by
      obtain ⟨⟨⟨⟨M, Cs, Hk, -, -, e⟩, RF⟩, one, r2⟩, QR, -⟩ := Ps
      rw [← e] at RF Fs
      obtain ⟨-, fitq, -, qsub, rdq, -⟩ := qTail QR.geo QR.q e10
      have eq := fun j (hj : j ≤ 27) => frameF_sv Cs.inp RF Fs hj
      obtain Cn : CtxOk (fun _ _ => True) base bytes len A .wide M
          (v.withRegions (v.rd ++ v.wr) [⟨base, bytes⟩]) :=
        ⟨VG.Proof.Ffdh.X86.In.narrow C.1 trivial, by
          show sv v.mem _ _ _ _ = _
          rw [eq 0 (by decide)]; exact Cs.mod, Cs.gt, Cs.odd, by
          show (_ * w32 v.mem base invOff + 1) % _ = _
          rw [frameF_inv Cs.inp RF Fs]; exact Cs.inv⟩
      obtain rdn : InRegions ((v.rd ++ v.wr) ++ [⟨base, bytes⟩]) (byteAddr (A 10)) (len - lead bs) :=
        let ⟨r, hr, hc⟩ := rdq
        ⟨r, List.mem_append_left _ (hrd r hr), hc⟩
      obtain apart := QR.geo.apart.sub_left qsub
      obtain h3 : sv v.mem base len .wide 3 = 1 := by rw [eq 3 (by decide)]; exact one
      obtain h4 : sv v.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % M := by
        rw [eq 4 (by decide), r2, Cs.mod]
      refine ⟨⟨⟨M, Cn, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
        ⟨C.1.top, fun r hr => by rw [List.mem_singleton.mp hr]; exact C.2.2⟩, C.2.1⟩, rdn, fitq, apart⟩, _,
        qRest_ok Cn h3 h4 e11 (by omega_arith) (by omega_arith) fitq rdn apart⟩
      have hj' : j ≤ 27 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith
      show sv v.mem _ _ _ _ < _
      rw [eq j hj']; exact Hk j hj
  unfold winQCall argCall
  refine RelCT.callBody (R := fun a b => ∃ s₁ s₂, Both (QPre Ex base bytes len args sp bs) s₁ s₂ ∧
      a = s₁.callEntry ∧ b = s₂.callEntry) ?_
    (fun s t h => ⟨s, t, h, rfl, rfl⟩) (fun _ _ h => (hP _ h.1).1.2.2.trans (hP _ h.2).1.2.2.symm)
  refine RelCT.frameAlloc (R := fun _ _ => True)
    (VG.RelCT.seq (R := Both (CalleeW (QPre Ex base bytes len args sp bs) base bytes len args sp)) ?_
      (VG.RelCT.seq (R := Both (CalleeQ (QPre Ex base bytes len args sp bs) base bytes len A sp)) ?_ ?_))
  · refine ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (hc := .block [])
      (by rfl)).wp (F₁ := CalleeW (QPre Ex base bytes len args sp bs) base bytes len args sp)
        (F₂ := CalleeW (QPre Ex base bytes len args sp bs) base bytes len args sp)
        fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    · obtain rfl := List.mem_singleton.mp hr
      obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨P₁, P₂⟩, rfl, rfl⟩, rfl, rfl⟩ := h
      rw [allocFrame_esp, allocFrame_esp, State.callEntry_esp, State.callEntry_esp, (hP _ P₁).1.2.2,
        (hP _ P₂).1.2.2]
    · obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨P₁, P₂⟩, rfl, rfl⟩, rfl, rfl⟩ := h
      obtain w : ∀ {x : State}, QPre Ex base bytes len args sp bs x →
          WP isa (.block ((List.range 18).flatMap copyArg)) (allocFrame argsFrame x.callEntry)
            (CalleeW (QPre Ex base bytes len args sp bs) base bytes len args sp) := fun {x} Px => by
        obtain ⟨R, F⟩ := hP x Px
        have e := R.2.2
        rw [← e] at F
        exact WP.mono (callee_atW R.1 F) fun u ⟨C, Fs, CI⟩ =>
          ⟨x, Px, by rw [← e]; exact C, by rw [← e]; exact Fs, CI, e⟩
      exact ⟨w P₁, w P₂⟩
  · refine ((RelCT.taint (A := taint) (τr [.esp, .edi]) (fun a b h => agree_regs fun r hr => ?_)
      setQ_check).wp (F₁ := CalleeQ (QPre Ex base bytes len args sp bs) base bytes len A sp)
        (F₂ := CalleeQ (QPre Ex base bytes len args sp bs) base bytes len A sp)
        fun a b h => ⟨wq a h.1, wq b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    obtain ⟨⟨_, _, C₁, -⟩, ⟨_, _, C₂, -⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [C₁.2.1, C₂.2.1]
    · exact BitVec.eq_of_toNat_eq (C₁.1.edi.trans C₂.1.edi.symm)
  · have cov : ∀ u, CalleeAt base bytes len A sp u →
        Covers ((u.rd ++ u.wr) ++ [⟨base, bytes⟩]) (u.rd ++ u.wr) ∧ Covers [⟨base, bytes⟩] u.wr := fun u C => by
      have c : Covers [⟨base, bytes⟩] u.wr :=
        Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact C.1.scratch.wr
      exact ⟨Covers.append_left (Covers.refl _) (Covers.right c), c⟩
    refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun u => u.rd ++ u.wr) (fun _ => [⟨base, bytes⟩])
      (Pn := Both fun w => WSt (fun _ _ => True) base bytes len A (sp - BitVec.ofNat 32 80) .wide [3, 4] 0 w ∧
        InRegions (w.rd ++ w.wr) (byteAddr (A 10)) (len - lead bs) ∧
        (A 10).toNat + (len - lead bs) ≤ 2 ^ 32 ∧
        Region.Disjoint ⟨byteAddr (A 10), len - lead bs⟩ ⟨base, bytes⟩)
      (fun f g ⟨Cf, Cg⟩ => ?_) ?_
    · obtain ⟨p₁, w₁⟩ := nar f Cf
      obtain ⟨p₂, w₂⟩ := nar g Cg
      obtain ⟨_, _, C₁, -⟩ := Cf
      obtain ⟨_, _, C₂, -⟩ := Cg
      exact ⟨(cov f C₁).1, (cov f C₁).2, (cov g C₂).1, (cov g C₂).2, w₁, w₂, p₁, p₂⟩
    · refine VG.RelCT.seq
        (R := Both (WSt (fun _ _ => True) base bytes len A (sp - BitVec.ofNat 32 80) .wide [3, 4] 0))
        (taint_both (fun _ _ W₁ W₂ => W₁.1.agree W₂.1) _ loadTopQ_check
          fun w ⟨⟨M, C, Hk, _, Aok, e⟩, rd, fit, apart⟩ => ?_)
        ((windowPowerWith_relCT (Ex := fun _ _ => True) (base := base) (bytes := bytes) (len := len) (args := A)
          (sp := sp - BitVec.ofNat 32 80) (winChecks .wide) (N := 2 * (len - lead bs)) (by omega_arith)
          (by omega_arith) lenCount_check fun _ W => lenCount_wst (by decide) e11 W).mono (fun _ _ h => h)
          fun _ _ _ => trivial)
      refine WP.mono (loadTopCtx_ok C (d := 8) (p := 10) (l := 11) (L := len - lead bs) (by decide) (by decide)
        (by decide) (by decide) e11 (by omega_arith) (by omega_arith) fit rd apart) fun u ⟨C', _, O, K⟩ =>
        ⟨M, C', fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _), Aok.keep K, (K.1 _ (by decide)).trans e⟩
      have hj' : j = 3 ∨ j = 4 := by simpa using hj
      rw [slotKeep C.inp (by omega_arith) (by omega_arith) O]; exact Hk j hj

/-- `winQCall`, with what each run reaches. -/
theorem winQCall_relCT :
    RelCT isa (Both (QPre Ex base bytes len args sp bs)) winQCall (Both (Run Ex base bytes len args sp)) := by
  refine relCT_both winQCall_trace fun x W => ?_
  obtain ⟨⟨⟨⟨M, C, -, -, Aok, e⟩, RF⟩, one, r2⟩, QR, Qat⟩ := W
  rw [← e] at RF
  exact WP.mono (winQCall_ok C QR.geo RF (by rw [e]; exact QR.hb40) one (by rw [r2, C.mod])
    (by rw [QR.q]; exact Qat)) fun u ⟨Cu, _, K, _⟩ => ⟨Cu.inp, Aok.keep K, (K.1 _ (by decide)).trans e⟩

/-- A power to q modulo p, after the scan: the base in slot `b`. -/
theorem powQ_trace {b : Nat} (hb9 : 9 ≤ b) (hb : b ≤ 17)
    (hcb : ACheck (copy (.slot .wide b) (.slot .wide 5) (one .wide))) :
    RelCT isa (Both fun u => QRun Ex base bytes len args sp bs u ∧ QAt base len args bs u.mem) (powQ b)
      (Both (Run Ex base bytes len args sp)) := by
  unfold powQ
  refine VG.RelCT.seq (R := Both (QPre Ex base bytes len args sp bs)) ?_
    (VG.RelCT.seq (R := Both (QPre Ex base bytes len args sp bs)) ?_ winQCall_relCT)
  · refine ((relCT_keep (X := fun u => QRun Ex base bytes len args sp bs u ∧ QAt base len args bs u.mem)
      ctxP_relCTF fun s R X => ?_).mono
        (fun _ _ h => ⟨⟨⟨h.1.1.run, h.1.1.room⟩, h.1⟩, ⟨⟨h.2.1.run, h.2.1.room⟩, h.2⟩⟩)
        fun _ _ h => ⟨⟨⟨⟨h.1.1.1, h.1.2.1.room⟩, h.1.1.2⟩, h.1.2⟩, ⟨⟨h.2.1.1, h.2.2.1.room⟩, h.2.1.2⟩, h.2.2⟩)
    obtain RF : RoomF (s.gpr .esp) base bytes := by rw [R.1.2.2]; exact R.2
    exact WP.mono (ctxP_ok R.1.1 RF rfl) fun u ⟨_, _, _, F, k, K⟩ =>
      ⟨X.1.step (Step.opsF R.1.1 RF F K), X.2.kept k⟩
  · refine relCT_keep (X := fun u => QRun Ex base bytes len args sp bs u ∧ QAt base len args bs u.mem)
      (copyWin_relCT hb9 hb (.inl rfl) hcb) fun s W X => ?_
    have h := W.1.1.run.1
    exact WP.mono (copyIn_ok h (j := b) (d := 5) hb9 (by omega_arith) (by decide)) fun u ⟨O, _, K⟩ =>
      ⟨X.1.step (Step.slot h (by decide) O K), X.2.kept (kept_slot h (a := 5) O)⟩

end

end VG.Proof.Ffdh.X86.QPower
