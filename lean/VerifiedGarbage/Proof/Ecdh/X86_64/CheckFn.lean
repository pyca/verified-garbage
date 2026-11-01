module

public import VerifiedGarbage.Proof.Ecdh.X86_64.Check
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Ecdh.Exchange

/-!
# `vg_<curve>_check_point` on x86-64: correctness

The facts of a curve's contract (`Proof/Weierstrass/CheckPointContract.lean`) for
x86-64, by name (`checkK`), for a configuration whose slots and numbers are
the curve's (`Agree`): `checkFn_ok` gives the flag `&=` the mask of the
point's validity, `x R` and `y R`, and the point for the scalar
multiplication; `invFnX_gpr` gives the callee-saved registers back
(`correct`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.CheckFn

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

/-- A curve of `Proof/Weierstrass/CheckPointContract.lean`. -/
abbrev CP := Impl.Weierstrass.CheckPoint.Curve

/-- `vg_<curve>_check_point`'s contract on x86-64, by name. -/
def checkK (C : CP) : Contract isa where
  pre s :=
    let ws : Region := ⟨s.gpr .rdi, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ ret.Disjoint ws ∧ (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64 ∧
      C.pre (s.gpr .rdi) s.mem
  post s s' := C.post (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

/-- The configuration `c` is the curve `C`'s: its curve, its words, its
slots but the temporary area's, and what the code writes is in the
function's own working space or its results. -/
structure Agree (c : Cfg) (C : CP) : Prop where
  W : c.C = C.W
  k : c.n = C.k
  sl : ∀ i < 45, i ≠ TMP → c.sl i = C.slot i
  keeps : ∀ (ws : Addr) (m m' : Mem), ws.toNat + 8192 ≤ 2 ^ 64 →
    Unch ws (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) m m' → C.Keeps ws m m'
  rsp : Reg.rsp ∉ checkClob c.n

/-- The number at an offset below `2³²` is the one `wordsVal` reads. -/
theorem num_eq (C : CP) (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    C.num ws m o = wordsVal m ws o C.k := by
  unfold Impl.Weierstrass.CheckPoint.Curve.num Impl.Weierstrass.Mont.numAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws C.k o

instance (C : CP) (i : Nat) : Decidable (C.Own i) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.Own; infer_instance

instance (C : CP) (i : Nat) : Decidable (C.Out i) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.Out; infer_instance

/-- `Keeps` from the ranges the code writes, each byte of which is in the own
working space or a result's. -/
theorem keeps_of {C : CP} {W : List (Nat × Nat)}
    (hW : ∀ w ∈ W, ∀ j < w.2, C.Own (w.1 + j) ∨ C.Out (w.1 + j)) (ws : Addr) (m m' : Mem)
    (_hfit : ws.toNat + 8192 ≤ 2 ^ 64) (hu : Unch ws W m m') : C.Keeps ws m m' := by
  intro i hi hown hout
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega)]
  by_contra hc
  have := hW w hw (i - w.1) (by omega)
  rw [show w.1 + (i - w.1) = i by omega] at this
  exact this.elim hown hout

/-- Whether the `l` bytes at `a` lie in one range of the own working space
or of a result's (`Own`, `Out`): what `keeps_of` asks of each written range,
for the kernel to decide once per range rather than once per byte. -/
def covers (C : CP) (a l : Nat) : Bool :=
  [2, 37, 41, 42].any (fun j => Nat.ble (C.slot j) a && Nat.ble (a + l) (C.slot j + 8 * C.k)) ||
    [34, 35, 38, 43].any (fun j => Nat.ble (C.slot j) a && Nat.ble (a + l) (C.slot j + 8 * C.k)) ||
    (Nat.ble (Impl.Weierstrass.Mont.ownAt C.k) a && Nat.ble (a + l) 4096) ||
    (Nat.ble C.flagAt a && Nat.ble (a + l) (C.flagAt + 8))

theorem own_or_out_of_covers {C : CP} {a l : Nat} (h : covers C a l = true) :
    ∀ j < l, C.Own (a + j) ∨ C.Out (a + j) := by
  intro j hj
  simp only [covers, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  unfold Impl.Weierstrass.CheckPoint.Curve.Own Impl.Weierstrass.CheckPoint.Curve.Out
  rcases h with ((⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact .inl (.inl ⟨i, hi, by omega, by omega⟩)
  · exact .inr (.inl ⟨i, hi, by omega, by omega⟩)
  · exact .inl (.inr ⟨by omega, by omega⟩)
  · exact .inr (.inr ⟨by omega, by omega⟩)

/-- `keeps_of`, from each written range lying in one range of `Own` or `Out`. -/
theorem keeps_of_covers {C : CP} {W : List (Nat × Nat)} (hW : W.all (fun w => covers C w.1 w.2) = true) :
    ∀ (ws : Addr) (m m' : Mem), ws.toNat + 8192 ≤ 2 ^ 64 → Unch ws W m m' → C.Keeps ws m m' :=
  keeps_of fun w hw => own_or_out_of_covers (List.all_eq_true.mp hW w hw)

variable {c : Cfg} {C : CP}

theorem slot_lt (hc : BaseCfgOk c) (A : Agree c C) {i : Nat} (hi : i < 45) : C.slot i < 2 ^ 32 := by
  have hk : C.k ≤ 9 := by have := hc.n10; rw [A.k] at this; omega
  have : 8 * C.k * i ≤ 8 * 9 * 45 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hk) (Nat.le_of_lt hi)
  unfold Impl.Weierstrass.CheckPoint.Curve.slot; omega

/-- A slot's number is the curve's. -/
theorem sv_eq (hc : BaseCfgOk c) (A : Agree c C) {i : Nat} (hi : i < 45) (ht : i ≠ TMP) (base : Addr)
    (m : Mem) : wordsVal m base (c.sl i) c.n = C.num base m (C.slot i) := by
  rw [A.sl i hi ht, A.k, num_eq C m base (slot_lt hc A hi)]

theorem flag_eq (A : Agree c C) (base : Addr) (m : Mem) :
    word m base (c.sl FLAG) = C.flag base m := by
  rw [A.sl FLAG (by decide) (by decide)]
  rfl

theorem mask_eq_zero {P : Prop} [Decidable P] : mask P = 0 ↔ ¬ P := by
  by_cases h : P <;> simp only [mask, h, ite_true, ite_false, not_true, not_false_eq_true]
  · decide

/-- The code's check of the curve's equation is the specification's. -/
theorem onCurve_iff' (C' : Spec.Weierstrass.Curve) (X Y : Fin C'.p) :
    onCurve C' (.affine X Y) = true ↔
      Y * Y - ((X * X * X + Fin.ofNat C'.p C'.a * X) + Fin.ofNat C'.p C'.b) = 0 := by
  rw [onCurve, decide_eq_true_iff]
  constructor <;> intro h <;> grind

/-- The checks of `x`, `y` and the curve's equation as the code states them,
on a curve `W` equal to `C`'s, are the specification's `Valid`. -/
theorem valid_iff (W : Spec.Weierstrass.Curve) (C : CP) (h : W = C.W) (x y : Nat) :
    (x < W.p ∧ y < W.p ∧ Fin.ofNat W.p y * Fin.ofNat W.p y - ((Fin.ofNat W.p x * Fin.ofNat W.p x *
      Fin.ofNat W.p x + Fin.ofNat W.p W.a * Fin.ofNat W.p x) + Fin.ofNat W.p W.b) = 0) ↔ C.Valid x y := by
  subst h
  unfold Impl.Weierstrass.CheckPoint.Curve.Valid
  rw [onCurve_iff']

/-- `correct`'s `hv` and `hmx` from one walk of the body: the instructions
`invFnX` adds around it load no MXCSR. -/
theorem hv_hmx {body : Prog isa}
    (h : body.allInstrs (fun i => !KeepReg.writesVec i && !loadsMxcsr i) = true) :
    body.allInstrs (fun i => !KeepReg.writesVec i) = true ∧
      (Cfg.invFnX body).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Code.allInstrs_eq, List.all_eq_true, Bool.and_eq_true] at h ⊢
  refine ⟨fun i hi => (h i hi).1, ?_⟩
  simp only [Cfg.invFnX, instrs, List.mem_append]
  rintro i (hi | hi | hi)
  · revert i; decide
  · exact (h i hi).2
  · revert i; decide

/-- `vg_<curve>_check_point`: the contract's postcondition and the ABI's
registers, from its precondition. -/
theorem correct (hc : BaseCfgOk c) (A : Agree c C)
    (hv : (Impl.Ecdh.X86_64.Cfg.checkBody c).allInstrs (fun i => !KeepReg.writesVec i) = true)
    (hn : (Impl.Ecdh.X86_64.Cfg.checkBody c).noCalls = true)
    (hmx : (Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody c)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (checkK C).pre s) :
    ∃ t s', Exec isa (Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody c)) s t s' ∧ abiPreserved s s' ∧
      (checkK C).post s s' := by
  obtain ⟨-, hwr, hret, hfit, hp, hr2, ha, hb, hfl⟩ := hs
  have hS : Scr s (s.gpr .rdi) size := ⟨rfl, by rw [hwr]; simp, hfit⟩
  have hR : c.R = C.R := by
    unfold Cfg.R Impl.Weierstrass.CheckPoint.Curve.R; rw [A.k]
  have hmp : sv c (s.gpr .rdi) s MP = c.C.p := by
    rw [sv, sv_eq hc A (by decide) (by decide), A.W]; exact hp
  have hap : sv c (s.gpr .rdi) s AP = c.mont c.C.a := by
    rw [sv, sv_eq hc A (by decide) (by decide), Cfg.mont, hR, A.W]; exact ha
  have hr2' : sv c (s.gpr .rdi) s R2P = c.R * c.R % c.C.p := by
    rw [sv, sv_eq hc A (by decide) (by decide), hR, A.W]; exact hr2
  have hbp : sv c (s.gpr .rdi) s BP = c.mont c.C.b := by
    rw [sv, sv_eq hc A (by decide) (by decide), Cfg.mont, hR, A.W]; exact hb
  have hf : word s.mem (s.gpr .rdi) (c.sl FLAG) =
      mask (C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64) := by
    rw [flag_eq A]
    rcases hfl with h | h <;> rw [h] <;> decide
  obtain ⟨t, s', he, P⟩ := checkFn_ok hc hS hmp hap hr2' hbp hf
  have hnc : (Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody c)).noCalls = true := by
    simp only [Cfg.invFnX, Code.noCalls, hn, Bool.and_true]
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have sv := invFnX_gpr hv hn he
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sv _ (by decide)
    · exact sv _ (by decide)
    · exact P.gpr _ A.rsp
    · exact sv _ (by decide)
    · exact sv _ (by decide)
    · exact sv _ (by decide)
    · exact sv _ (by decide)
  · have F := (Exec.regions he hnc).2.2
    rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl; exact hret) (by decide)
  -- The postcondition.
  have eX : sv c (s.gpr .rdi) s E = C.num (s.gpr .rdi) s.mem C.xAt := sv_eq hc A (by decide) (by decide) _ _
  have eY : sv c (s.gpr .rdi) s QY = C.num (s.gpr .rdi) s.mem C.yAt := sv_eq hc A (by decide) (by decide) _ _
  have hP : CheckOk c (s.gpr .rdi) s (C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64) ↔
      C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64 ∧
        C.Valid (C.num (s.gpr .rdi) s.mem C.xAt) (C.num (s.gpr .rdi) s.mem C.yAt) := by
    simp only [CheckOk, PeerOk, OnCurve, eX, eY]
    rw [← valid_iff c.C C A.W]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩; exact ⟨h₁, h₂, h₃, h₄⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩; exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
  have hF : C.flag (s.gpr .rdi) s'.mem = C.flag (s.gpr .rdi) s.mem &&&
      Impl.Weierstrass.CheckPoint.Curve.mask
        (C.Valid (C.num (s.gpr .rdi) s.mem C.xAt) (C.num (s.gpr .rdi) s.mem C.yAt)) := by
    rw [← flag_eq A, P.flag]
    have hm : Impl.Weierstrass.CheckPoint.Curve.mask
        (C.Valid (C.num (s.gpr .rdi) s.mem C.xAt) (C.num (s.gpr .rdi) s.mem C.yAt)) =
        mask (C.Valid (C.num (s.gpr .rdi) s.mem C.xAt) (C.num (s.gpr .rdi) s.mem C.yAt)) := rfl
    rw [hm]
    have h0 : C.flag (s.gpr .rdi) s.mem = mask (C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64) := by
      rcases hfl with h | h <;> rw [h] <;> decide
    conv => rhs; rw [h0]
    rw [mask_and]
    simp only [mask, hP]
  have hok : CheckOk c (s.gpr .rdi) s (C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64) ↔
      ¬ (C.flag (s.gpr .rdi) s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask
        (C.Valid (C.num (s.gpr .rdi) s.mem C.xAt) (C.num (s.gpr .rdi) s.mem C.yAt)) = 0) := by
    rw [← hF, ← flag_eq A (s.gpr .rdi) s'.mem, P.flag, mask_eq_zero, not_not]
  have hRp : 2 ^ (64 * c.n) = C.R := by rw [← hR]; rfl
  refine ⟨hF, ?_, ?_, ?_, ?_, A.keeps _ _ _ hfit P.unch⟩
  · show C.num _ _ (C.slot QXM) = _
    rw [← sv_eq hc A (i := QXM) (by decide) (by decide)]
    show sv c _ s' QXM = _
    rw [P.qxm, eX, hRp, A.W]
  · show C.num _ _ (C.slot QYM) = _
    rw [← sv_eq hc A (i := QYM) (by decide) (by decide)]
    show sv c _ s' QYM = _
    rw [P.qym, eY, hRp, A.W]
  · show C.num _ _ (C.slot PX) = _
    rw [← sv_eq hc A (i := PX) (by decide) (by decide)]
    show sv c _ s' PX = _
    rw [P.px]
    by_cases h : CheckOk c (s.gpr .rdi) s (C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false (hok.mp h)), eX, hRp, A.W]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true (not_not.mp (mt hok.mpr h))), sv, sv_eq hc A (i := GX) (by decide) (by decide)]; rfl
  · show C.num _ _ (C.slot PY) = _
    rw [← sv_eq hc A (i := PY) (by decide) (by decide)]
    show sv c _ s' PY = _
    rw [P.py]
    by_cases h : CheckOk c (s.gpr .rdi) s (C.flag (s.gpr .rdi) s.mem = BitVec.allOnes 64)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false (hok.mp h)), eY, hRp, A.W]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true (not_not.mp (mt hok.mpr h))), sv, sv_eq hc A (i := GY) (by decide) (by decide)]; rfl

/-! ## Constant time, and the shared contract -/

theorem agreeK (C : CP) (s₁ s₂ : State) (_ : (checkK C).pre s₁) (_ : (checkK C).pre s₂)
    (h : (checkK C).pub s₁ s₂) : VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsp]) s₁ s₂ :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2
    · exact h.1

/-- A working space at `0x1000` holding `p`, `R² mod p`, `a R mod p` and
`b R mod p` where the curve's contract says, and zeros elsewhere (the flag
zero). -/
def satMem (C : CP) : Mem := fun a =>
  let i := (a - 0x1000).toNat
  let at_ (o v : Nat) : Option Nat := if o ≤ i ∧ i < o + 8 * C.k then some (v >>> (8 * (i - o))) else none
  match at_ C.pAt C.W.p with
  | some v => BitVec.ofNat 8 v
  | none => match at_ C.r2At (C.R * C.R % C.W.p) with
    | some v => BitVec.ofNat 8 v
    | none => match at_ C.aAt (C.W.a * C.R % C.W.p) with
      | some v => BitVec.ofNat 8 v
      | none => match at_ C.bAt (C.W.b * C.R % C.W.p) with
        | some v => BitVec.ofNat 8 v
        | none => 0

/-- A state satisfying the preconditions, for a curve whose working space
`satMem` satisfies them. -/
def satState (C : CP) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem C
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_of (C : CP) (h : C.pre 0x1000 (satMem C)) : (checkK C).pre (satState C) :=
  ⟨rfl, rfl, Region.disjoint_of_sep (show Region.sep ⟨0x20000, 8⟩ ⟨0x1000, 8192⟩ = true by decide),
    show (0x1000 : BitVec 64).toNat + 8192 ≤ 2 ^ 64 by decide, h⟩

theorem implies (C : CP) (hsat : C.pre 0x1000 (satMem C)) : (checkK C).Implies (C.checkContract X86_64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      X86_64.abi, X86_64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      X86_64.abi, X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact h
  sat := ⟨satState C, by
    sig_pre [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      X86_64.abi, X86_64.argRegs, stackBelow]
    exact ⟨Region.disjoint_of_sep (by decide), by decide, hsat⟩⟩

end VG.Proof.Ecdh.X86_64.CheckFn
