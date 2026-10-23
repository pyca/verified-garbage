module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Kernel
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Framework.Omega

/-! # A function around the kernel

`body params`: the callee-saved registers pushed, `params` setting the
kernel's parameters in registers, which a frame of 28 bytes pushes, the
kernel, then the registers back (`body_ok`). Its frames and the kernel's MCDT
frame use the 56 bytes below `esp`, apart from the working space (`Entry`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar ofs_far)

/-- The stack on entry: `esp`, its 56 bytes below apart from the working space. -/
structure Entry (s : State) (W : Addr) (L : Nat) : Prop where
  lo : 56 ≤ (s.gpr .esp).toNat
  hi : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  ws : Ws s W L
  far : ∀ j < 60, L ≤ ofs W ((s.gpr .esp).setWidth 64 - 56 + BitVec.ofNat 64 j)

/-- A stack address `c` bytes below `esp` plus `k`, from the bottom of the 56 bytes. -/
theorem stack_addr {sp : BitVec 32} (hlo : 56 ≤ sp.toNat) (hhi : sp.toNat + 24 ≤ 2 ^ 32) {c k : Nat}
    (hc : c ≤ 56) (hk : k < c + 24) :
    (sp - BitVec.ofNat 32 c + BitVec.ofNat 32 k).setWidth 64 = sp.setWidth 64 - 56 + BitVec.ofNat 64 (56 - c + k) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (56 : BitVec 64).toNat = 56 from rfl]
  omega

/-- The values the kernel's frame of parameters holds, from the registers. -/
def vals (t : State) (i : Nat) : BitVec 32 := t.gpr (([.ebp, .edi, .esi, .edx, .ecx, .ebx, .eax] : List Reg).getD i .eax)

/-- The registers the frame of parameters pushes, last pushed first. -/
abbrev rs7 : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

theorem vals_eq (t : State) {i : Nat} (hi : i < 7) : vals t i = t.gpr rs7[rs7.length - 1 - i] := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

theorem add_ofNat64 (a : Addr) (d j : Nat) : a + BitVec.ofNat 64 d + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (d + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The frame of parameters, 44 bytes below the entry's `esp`. -/
theorem params_pushed {t : State} {W : Addr} {L : Nat} {sp : BitVec 32} (hlo : 56 ≤ sp.toNat)
    (hhi : sp.toNat + 24 ≤ 2 ^ 32) (hesp : t.gpr .esp = sp - 16)
    (far : ∀ j < 60, L ≤ ofs W (sp.setWidth 64 - 56 + BitVec.ofNat 64 j)) :
    Params (pushed rs7 t) W L (vals t) 0 := by
  have e7 : (pushed rs7 t).gpr .esp = sp - 16 - 28 := by rw [pushed_esp, hesp]; rfl
  have ea : ∀ i < 7, (pushed rs7 t).ea (prm 0 i) = sp.setWidth 64 - 56 + BitVec.ofNat 64 (12 + 4 * i) := by
    intro i hi
    simp only [State.ea, prm, at_, e7, Nat.zero_add]
    rw [show sp - 16 - 28 = sp - BitVec.ofNat 32 44 by rw [BitVec.sub_sub]; rfl, stack_addr hlo hhi (by decide) (by omega)]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · show (pushed rs7 t).load32 ((pushed rs7 t).ea (prm 0 i)) = _
    have hs16 : (sp - 16).toNat = sp.toNat - 16 := by
      rw [BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl]; omega
    have hn7 : 4 * rs7.length ≤ (t.gpr .esp).toNat := by rw [hesp, hs16]; simp only [List.length_cons, List.length_nil]; omega
    have w := pushed_word (rs := rs7) (s := t) (by decide) hn7 (i := i) (by simpa using hi)
    rw [State.load32, ite_eq_left_iff.mpr fun h => absurd ?_ h, vals_eq t hi]
    · simp only [State.ea, prm, at_, Nat.zero_add]; rw [w]
    · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      rw [ea i hi]
      simp only [Region.Contains, hesp, List.length_cons, List.length_nil]
      have := sp.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [show (56 : BitVec 64).toNat = 56 from rfl, show (16 : BitVec 32).toNat = 16 from rfl]
      omega
  · rw [ea i hi, add_ofNat64]; exact far _ (by omega)

/-- A byte of a frame within the 56 bytes below the entry's `esp` lies past the working space. -/
theorem below_far {s : State} {W : Addr} {L : Nat} (E : Entry s W L) {c n : Nat} (hc : c + n ≤ 56) (hn : 0 < n)
    {x : Addr} (hx : (below (s.gpr .esp - BitVec.ofNat 32 c) n).Contains x 1) : L ≤ ofs W x := by
  have hlo := E.lo
  have hhi := E.hi
  have e : x = (s.gpr .esp).setWidth 64 - 56 + BitVec.ofNat 64 (56 - c - n + (x - (s.gpr .esp - BitVec.ofNat 32 c -
      BitVec.ofNat 32 n).setWidth 64).toNat) := by
    have := (s.gpr .esp).isLt
    simp only [Region.Contains] at hx
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hx ⊢
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    have := x.isLt
    omega
  rw [e]
  simp only [Region.Contains] at hx
  exact E.far _ (by omega)

/-- The working space's bytes past the frames' pushes. -/
theorem frame_ws {s : State} {W : Addr} {L : Nat} (E : Entry s W L) {c n : Nat} (hc : c + n ≤ 56) (hn : 0 < n)
    {m m' : Mem} (F : Frame [below (s.gpr .esp - BitVec.ofNat 32 c) n] m m') : Outs W [(L, 2 ^ 64)] m m' :=
  fun x hx => F x fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    intro h
    have := below_far E hc hn h
    have := hx _ (List.mem_singleton_self _)
    have : ofs W x < 2 ^ 64 := (x - W).isLt
    simp only at *; omega

theorem kernel_noSp : NoSp kernel := NoSp.of_all (by decide +kernel)

abbrev rs4 : List Reg := [.ebx, .esi, .edi, .ebp]

/-- The byte `d` of the stack from 56 bytes below `sp`. -/
abbrev stk (sp : BitVec 32) (d : Nat) : Addr := sp.setWidth 64 - 56 + BitVec.ofNat 64 d

theorem below_contains {sp base : BitVec 32} (hlo : 56 ≤ sp.toNat) (hhi : sp.toNat + 24 ≤ 2 ^ 32) {c n d : Nat}
    (hb : base = sp - BitVec.ofNat 32 c) (hc : c + n ≤ 56) (hd : d < 60) :
    (below base n).Contains (stk sp d) 1 ↔ (56 - c - n ≤ d ∧ d < 56 - c) := by
  subst hb
  have := sp.isLt
  simp only [Region.Contains, stk, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [show (56 : BitVec 64).toNat = 56 from rfl]
  omega

theorem stk_inj {sp : BitVec 32} {d e : Nat} (hd : d < 60) (he : e < 60)
    (h : stk sp d = stk sp e) : d = e := by
  have h' : (sp.setWidth 64 - 56 + BitVec.ofNat 64 d).toNat = (sp.setWidth 64 - 56 + BitVec.ofNat 64 e).toNat := by
    rw [show sp.setWidth 64 - 56 + BitVec.ofNat 64 d = stk sp d from rfl, h]
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
  rw [show (56 : BitVec 64).toNat = 56 from rfl] at h'
  omega

/-- A byte of a frame below `sp - c` is among the 56 bytes below `sp`. -/
theorem below_sub {sp base : BitVec 32} (hlo : 56 ≤ sp.toNat) {c n : Nat} (hb : base = sp - BitVec.ofNat 32 c)
    (hc : c + n ≤ 56) {x : Addr} (h : (below base n).Contains x 1) : (below sp 56).Contains x 1 := by
  subst hb
  have := sp.isLt
  have := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h ⊢
  omega

/-- `pop r` `k + 1` times leaves in `r` the frame's last word. -/
theorem popReg_last (s : State) {d : Reg} (hd : d ≠ .esp) (k : Nat) :
    (popReg s d (k + 1)).gpr d = s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 := by
  induction k generalizing s with
  | zero => simp [popReg, State.setReg, hd]
  | succ k ih =>
    rw [popReg, ih]
    simp only [State.setReg, ite_true, Ne.symm hd, ite_false, BitVec.add_assoc]
    congr 3
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]; congr 1; omega

/-- What `params` leaves, from the state `s` before the callee-saved
registers' push: the kernel's parameters in registers. -/
def ParamsPost (s : State) (W : Addr) (N S mo inv o a b : Nat) (t : State) : Prop :=
  PVals (vals t) W N S mo inv o a b ∧ t.gpr .esp = s.gpr .esp - 16 ∧ t.mem = (pushed rs4 s).mem ∧
    t.rd = s.rd ∧ t.wr = (pushed rs4 s).wr

/-- The kernel's entry, after the frame of parameters' push. -/
theorem kernel_ready {s t1 : State} {W : Addr} {L N S mo inv o a b : Nat}
    (E : Entry s W L) (Ly : Lay L N S mo inv o a b)
    (hinv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) (H : ParamsPost s W N S mo inv o a b t1) :
    KReady (pushed rs7 t1) W L N S mo inv o a b (vals t1) := by
  obtain ⟨PV, esp1, m1, -, wr1⟩ := H
  have hlo := E.lo
  have hhi := E.hi
  have hn := E.ws.nowrap
  have hs16 : (s.gpr .esp - 16).toNat = (s.gpr .esp).toNat - 16 := by
    rw [BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl]; omega
  have hn7 : 4 * rs7.length ≤ (t1.gpr .esp).toNat := by
    rw [esp1, hs16]; simp only [List.length_cons, List.length_nil]; omega
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl, ← m1] at F1
  have F2 := pushed_frame (rs := rs7) (s := t1) (by decide) hn7
  rw [show 4 * rs7.length = 28 from rfl] at F2
  have esp2 : (pushed rs7 t1).gpr .esp = s.gpr .esp - 44 := by
    rw [pushed_esp, esp1, BitVec.sub_sub]; rfl
  have O2 : Outs W [(L, 2 ^ 64)] s.mem (pushed rs7 t1).mem := by
    refine (frame_ws E (c := 0) (n := 16) (by decide) (by decide) (by simpa using F1)).trans
      (frame_ws E (c := 16) (n := 28) (by decide) (by decide) (by rw [esp1] at F2; exact F2))
  have ws2 : ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (pushed rs7 t1).mem W d k = val32 s.mem W d k := fun hd =>
    O2.val32 (by simp only [List.mem_singleton, forall_eq]; omega) (by omega)
  have w2 : ∀ {d : Nat}, d + 4 ≤ L → w32 (pushed rs7 t1).mem W d = w32 s.mem W d := fun {d} hd => by
    have := ws2 (d := d) (k := 1) (by omega)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  have hs44 : (s.gpr .esp - 44).toNat = (s.gpr .esp).toNat - 44 := by
    rw [BitVec.toNat_sub, show (44 : BitVec 32).toNat = 44 from rfl]; omega
  have hm2 : (pushed rs7 t1).gpr .esp - 12 = s.gpr .esp - BitVec.ofNat 32 56 + BitVec.ofNat 32 0 := by
    rw [esp2, BitVec.sub_sub, BitVec.add_zero]; rfl
  refine ⟨Ly, PV, ⟨by rw [pushed_wr, wr1, pushed_wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ E.ws.wr), hn⟩,
    params_pushed hlo hhi esp1 E.far, by rw [esp2, hs44]; omega, by rw [esp2, hs44]; omega, fun j hj => ?_,
    by rw [w2 (by have := Ly.mo_le; have := Ly.hN; omega), w2 Ly.inv_le]; exact hinv,
    by rw [ws2 Ly.b_le, ws2 Ly.mo_le]; exact hB⟩
  rw [hm2, stack_addr hlo hhi (c := 56) (k := 0) (by decide) (by omega), add_ofNat64]
  exact E.far _ (by omega)

/-- What `body params` leaves, for `params` setting the parameters from the
state after the callee-saved registers' push. -/
theorem body_ok {s : State} {params : List Instr} {W : Addr} {L N S mo inv o a b : Nat}
    (E : Entry s W L) (Ly : Lay L N S mo inv o a b)
    (hns : NoSp (seqs [.block params, withParams, .block restoreRegs]))
    (hp : WP isa (.block params) (pushed rs4 s) fun t =>
      PVals (vals t) W N S mo inv o a b ∧ t.gpr .esp = s.gpr .esp - 16 ∧ t.mem = (pushed rs4 s).mem ∧
        t.rd = s.rd ∧ t.wr = (pushed rs4 s).wr)
    (hinv : (w32 s.mem W mo * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) :
    WP isa (body params) s fun u =>
      val32 u.mem W o N < val32 s.mem W mo N ∧
      val32 u.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W b N % val32 s.mem W mo N ∧
      (∀ x, (∀ r ∈ [(S, 8 * N + 28), (o, 4 * N)], ofs W x < r.1 ∨ r.1 + r.2 ≤ ofs W x) →
        ¬ (below (s.gpr .esp) 56).Contains x 1 → u.mem x = s.mem x) ∧
      (∀ r ∈ calleeSaved, u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hlo := E.lo
  have hhi := E.hi
  have hn := E.ws.nowrap
  have hs16 : (s.gpr .esp - 16).toNat = (s.gpr .esp).toNat - 16 := by
    rw [BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl]; omega_arith
  unfold body
  refine WP.frame (rs := rs4) (r := .ebx) (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega_arith) hns ?_
  simp only [seqs]
  refine WP.seq (WP.mono hp fun t1 ⟨PV, esp1, m1, rd1, wr1⟩ => ?_)
  have hn7 : 4 * rs7.length ≤ (t1.gpr .esp).toNat := by
    rw [esp1, hs16]; simp only [List.length_cons, List.length_nil]; omega_arith
  refine WP.seq (WP.frame (rs := rs7) (r := .eax) (by decide) (by decide) (by decide) hn7 kernel_noSp ?_)
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl, ← m1] at F1
  have F2 := pushed_frame (rs := rs7) (s := t1) (by decide) hn7
  rw [show 4 * rs7.length = 28 from rfl] at F2
  have esp2 : (pushed rs7 t1).gpr .esp = s.gpr .esp - 44 := by
    rw [pushed_esp, esp1, BitVec.sub_sub]; rfl
  -- The working space's bytes, as on entry.
  have O2 : Outs W [(L, 2 ^ 64)] s.mem (pushed rs7 t1).mem := by
    refine (frame_ws E (c := 0) (n := 16) (by decide) (by decide) (by simpa using F1)).trans
      (frame_ws E (c := 16) (n := 28) (by decide) (by decide) (by rw [esp1] at F2; exact F2))
  have ws2 : ∀ {d k : Nat}, d + 4 * k ≤ L → val32 (pushed rs7 t1).mem W d k = val32 s.mem W d k := fun hd =>
    O2.val32 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  have w2 : ∀ {d : Nat}, d + 4 ≤ L → w32 (pushed rs7 t1).mem W d = w32 s.mem W d := fun {d} hd => by
    have := ws2 (d := d) (k := 1) (by omega_arith)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  have hw2 : Ws (pushed rs7 t1) W L :=
    ⟨by rw [pushed_wr, wr1, pushed_wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ E.ws.wr), hn⟩
  have hs44 : (s.gpr .esp - 44).toNat = (s.gpr .esp).toNat - 44 := by
    rw [BitVec.toNat_sub, show (44 : BitVec 32).toNat = 44 from rfl]; omega_arith
  have hm2 : ∀ j < 8, (pushed rs7 t1).gpr .esp - 12 = s.gpr .esp - BitVec.ofNat 32 56 + BitVec.ofNat 32 0 := by
    intro _ _; rw [esp2, BitVec.sub_sub, BitVec.add_zero]; rfl
  refine WP.mono (kernel_ok (kernel_ready E Ly hinv hB ⟨PV, esp1, m1, rd1, wr1⟩))
    fun v ⟨lt, cong, mv, Kv⟩ => ?_
  rw [show rs7.length = 7 from rfl]
  -- After the kernel's frame: the saved registers.
  have espv : v.gpr .esp = s.gpr .esp - 44 := by rw [Kv.1 _ (by decide), esp2]
  have espw : (popped .eax 7 v).gpr .esp = s.gpr .esp - 16 := by
    rw [popped_esp, espv, BitVec.sub_add_comm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (44 : BitVec 32).toNat = 44 from rfl, show (16 : BitVec 32).toNat = 16 from rfl]
    have := (s.gpr .esp).isLt
    omega_arith
  have wrw : (popped .eax 7 v).wr = below (s.gpr .esp) 16 :: s.wr := by
    rw [popped_wr, Kv.2.2, pushed_wr, wr1, pushed_wr]; rfl
  have rdw : (popped .eax 7 v).rd = s.rd := by rw [popped_rd, Kv.2.1, pushed_rd, rd1]
  -- A stack byte above the kernel's frames is as the first push left it.
  have mw : ∀ d, 40 ≤ d → d < 60 → (popped .eax 7 v).mem (stk (s.gpr .esp) d) = (pushed rs4 s).mem (stk (s.gpr .esp) d) := by
    intro d hd1 hd2
    rw [popped_mem, mv _ (fun j hj h => by
        rw [hm2 j hj, stack_addr hlo hhi (c := 56) (k := 0) (by decide) (by omega_arith), add_ofNat64] at h
        have := stk_inj (sp := s.gpr .esp) (by omega_arith) (by omega_arith) h
        omega_arith)
      (fun r hr => by
        have hf : L ≤ ofs W (stk (s.gpr .esp) d) := E.far d hd2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have := Ly.s_le
        have := Ly.o_le
        rcases hr with rfl | rfl <;> simp only <;> omega_arith),
      F2 _ (fun r hr h => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [below_contains hlo hhi (c := 16) (n := 28) esp1 (by decide) (by omega_arith)] at h
        omega_arith), m1]
  have saved : ∀ i < 4, readSrc (popped .eax 7 v) (.mem (at_ .esp (4 * i))) = some (s.gpr rs4[rs4.length - 1 - i]) := by
    intro i hi
    have ea : (popped .eax 7 v).ea (at_ .esp (4 * i)) = stk (s.gpr .esp) (40 + 4 * i) := by
      simp only [State.ea, at_, espw]
      rw [show s.gpr .esp - 16 = s.gpr .esp - BitVec.ofNat 32 16 from rfl, stack_addr hlo hhi (by decide) (by omega_arith)]
    show (popped .eax 7 v).load32 _ = _
    rw [ea, State.load32, ite_eq_left_iff.mpr fun h => absurd ?_ h]
    · have w := pushed_word (rs := rs4) (s := s) (by decide) h16 (i := i) hi
      rw [pushed_esp, show 4 * rs4.length = 16 from rfl] at w
      rw [show ((s.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)).setWidth 64 : Addr) =
        stk (s.gpr .esp) (40 + 4 * i) from stack_addr hlo hhi (by decide) (by omega_arith)] at w
      rw [← w, Mem.readW_congr fun j hj => ?_]
      rw [show stk (s.gpr .esp) (40 + 4 * i) + BitVec.ofNat 64 j = stk (s.gpr .esp) (40 + 4 * i + j) from
        add_ofNat64 _ _ _]
      exact mw _ (by omega_arith) (by omega_arith)
    · rw [rdw, wrw]
      refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      have := (s.gpr .esp).isLt
      simp only [Region.Contains, stk, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat]
      rw [show (56 : BitVec 64).toNat = 56 from rfl]
      omega_arith
  -- The callee-saved registers back.
  unfold restoreRegs
  refine wp_movS (saved 0 (by decide)) fun z1 y1 _ =>
    wp_movS ((Dynamic.readSrc_upd y1 (by decide)).trans (saved 1 (by decide))) fun z2 y2 _ =>
    wp_movS (((Dynamic.readSrc_upd y2 (by decide)).trans (Dynamic.readSrc_upd y1 (by decide))).trans
      (saved 2 (by decide))) fun z3 y3 _ => WP.block_nil ?_
  rw [show rs4.length = 4 from rfl]
  have g3 : ∀ r, r ≠ .ebp → r ≠ .edi → r ≠ .esi → z3.gpr r = (popped .eax 7 v).gpr r := fun r h1 h2 h3 => by
    rw [y3.other _ h3, y2.other _ h2, y1.other _ h1]
  have mem3 : z3.mem = (popped .eax 7 v).mem := by rw [y3.mem, y2.mem, y1.mem]
  have esp3 : z3.gpr .esp = s.gpr .esp - 16 := by rw [g3 _ (by decide) (by decide) (by decide), espw]
  have ebx3 : (popped .ebx 4 z3).gpr .ebx = s.gpr .ebx := by
    have h := saved 3 (by decide)
    simp only [readSrc, State.load32] at h
    split at h
    · simp only [Option.some.injEq] at h
      show (popReg z3 .ebx (3 + 1)).gpr .ebx = _
      rw [popReg_last _ (by decide), esp3, mem3, show s.gpr .ebx = s.gpr rs4[rs4.length - 1 - 3] from rfl, ← h]
      simp only [State.ea, at_, espw]
    · cases h
  have mu : (popped .ebx 4 z3).mem = v.mem := by rw [popped_mem, mem3, popped_mem]
  have hw0 : val32 v.mem W o N = val32 v.mem W o N := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mu, ← ws2 Ly.mo_le]; exact lt
  · rw [mu, ← ws2 Ly.mo_le, ← ws2 Ly.a_le, ← ws2 Ly.b_le]; exact cong
  · intro x hr hb
    rw [mu, mv x (fun j hj h => hb (by
        rw [h, hm2 j hj, stack_addr hlo hhi (c := 56) (k := 0) (by decide) (by omega_arith), add_ofNat64]
        rw [below_contains hlo hhi (c := 0) (n := 56) (by simp) (by decide) (by omega_arith)]
        omega_arith)) hr,
      F2 x (fun r h h' => by
        simp only [List.mem_singleton] at h; subst h
        exact hb (below_sub hlo (c := 16) (n := 28) esp1 (by decide) h')),
      F1 x (fun r h h' => by
        simp only [List.mem_singleton] at h; subst h
        exact hb (below_sub hlo (c := 0) (n := 16) (by simp) (by decide) h'))]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ebx3
    · rw [popped_gpr _ _ _ (by decide) (by decide), y3.gpr]; rfl
    · rw [popped_gpr _ _ _ (by decide) (by decide), y3.other _ (by decide), y2.gpr]; rfl
    · rw [popped_gpr _ _ _ (by decide) (by decide), y3.other _ (by decide), y2.other _ (by decide), y1.gpr]; rfl
    · rw [popped_esp, esp3, show BitVec.ofNat 32 (4 * 4) = 16 from rfl, BitVec.sub_add_cancel]
  · rw [popped_rd, y3.rd, y2.rd, y1.rd, rdw]
  · rw [popped_wr, y3.wr, y2.wr, y1.wr, wrw]; rfl

end VG.Proof.Mont.X86.Sse2
