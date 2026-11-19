module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Timing
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Recode
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Timing
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Recode
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
meta import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import Mathlib.FieldTheory.Finite.Basic
meta import Mathlib.Tactic.NormNum.Prime
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLocal
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyRoot
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLocal
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyRoot
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ed448.X86_64.VerifyPrefix`, which only this module used -/

section

/-! The fixed-address prefix initializes all public verification digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (BITS)

/-- Everything before the joint multiplication. -/
def verifyPrefix (fld : Impl.X448.X86_64.Field) (rt : Prog isa) : Prog isa :=
  .seq (.seq (.seq (.seq (.block ventry) vbits) (.block vstart)) (vdecode fld rt)) (.block (vnegA fld))

theorem verifyPrefix_ok {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)
    (hR : RecoverOk) {rt : Prog isa} (hrt : RootOk rt) {s : State} (hp : verifyEquationLocal.pre s) :
    WP isa (verifyPrefix fld rt) s (Window.JointTimingCtx (s.gpr .rcx) (signatureScalar s) (challengeScalar s)) := by
  obtain ⟨hr, hw, hdk, hds, hdc, hret, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rcx = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hret hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdi, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega_using [h])⟩
  have rsg : ∀ i n, i + n ≤ 114 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rsi, 114⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 114) h (by omega_using [h])⟩
  have rch : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdx, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega_using [h])⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdi + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hds (by omega_using [hi]) (by decide)
  have fs : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) :=
    fun i hi => by rw [Offset.add_add]; exact far hds (by omega_using [hi]) (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = K := ⟨_, rfl⟩
  rw [verifyPrefix]
  apply WP.assoc'
  apply WP.assoc'
  apply WP.assoc'
  -- The entry: the callee-saved registers saved, and the pointers.
  apply WP.seq
  refine WP.mono (ventry_ok hbase hws hn) fun s1 ⟨hs1, sv1, r81, r91, si1, g1, o1, rd1, wr1⟩ => ?_
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [rd1, wr1]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `k` and `S`.
  apply WP.seq
  refine WP.mono (vbits_ok (sig := s.gpr .rsi) (ch := s.gpr .rdx) hs1 si1 r91
    (fun q hq => by rw [rr1, Offset.add_add]; exact rsg _ _ (by omega_using [hq]))
    (fun q hq => by rw [rr1]; exact rch _ _ (by omega_using [hq])) fs fch)
    fun s2 ⟨bs2, bk2, si2, g2, rd2, wr2, o2⟩ => ?_
  rw [far_bytes O1 fs, hS] at bs2
  rw [far_bytes O1 fch, hK] at bk2
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hn⟩
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rd1, wr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  -- The pointers saved, and the check of `S`.
  apply WP.seq
  refine WP.mono (vstart_ok (pk := s.gpr .rdi) (sig := s.gpr .rsi) hs2 (by rw [g2 _ (by decide), r81]) (by rw [g2 _ (by decide), r91]) si2
    (fun i hi => by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega_using [hi]))
    (by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega_using [])) fs)
    fun s3 ⟨pk3, sig3, ⟨c0, hc0, b3⟩, g3, rd3, wr3, o3⟩ => ?_
  rw [far_bytes O2 fs, hS] at hc0
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hn⟩
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [rd3, wr3, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (o3.mono (by decide) (by decide))
  -- `R` and `A`, decoded by one loop.
  apply WP.seq
  refine WP.mono (vdecode_ok hf hR hrt hs3 pk3 sig3 (fun i n h => by rw [rr3]; exact rpk i n h)
    (fun i n h => by rw [rr3]; exact rsg i n (by omega_using [h])) fpk fsg)
    fun s4 ⟨⟨cR, cA, hcR, hcA, b4⟩, vr4, va4, g4, rd4, wr4, D4⟩ => ?_
  rw [far_bytes O3 fpk] at hcA va4
  rw [far_bytes O3 fsg, ← bytesAt_take57] at hcR vr4
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hn⟩
  have O4 : Outside base 0 8192 s.mem s4.mem := O3.trans (D4.wide.mono (by decide) (by decide))
  -- `A` negated, and the constants.
  refine WP.mono (vnegA_ok hf hs4) fun s4' ⟨n6, n7, n10, p4, q4, d4, g4', rd4', wr4', o4⟩ => ?_
  have hs4' : Scr s4' base := ⟨(g4' _ (by decide)).trans hs4.rdi, wr4' ▸ hs4.wr, hn⟩
  have bits4 : ∀ o : Nat, o + 460 ≤ 8192 → 2048 ≤ o → ∀ t < 461,
      s4'.mem (off base (o - 1 + t)) = s2.mem (off base (o - 1 + t)) := fun o ho1 ho2 t ht => by
    have hofs := VG.Proof.X448.X86_64.ofs_off' base (d := o - 1 + t) (by omega_using [ho1, ht])
    rw [o4 _ (Or.inr (by rw [hofs]; omega_using [ho2])), D4.wide _ (Or.inr (by rw [hofs]; omega_using [ho2])),
      o3 _ (Or.inr (by rw [hofs]; simp only [KC]; omega_using [ho2]))]
  have bs4 : Window.Bits base BITS S s4' := by
    intro t ht
    rw [bits4 BITS (by decide) (by decide) t ht, bs2 t ht]
  have bk4 : Window.Bits base KBITS K s4' := by
    intro t ht
    rw [bits4 KBITS (by decide) (by decide) t ht, bk2 t ht]
  simpa only [signatureScalar, challengeScalar, hS, hK, hbase] using
    (show Window.JointTimingCtx base S K s4' from ⟨hs4', bs4, bk4, d4, n10, p4⟩)

end VG.Proof.Ed448.X86_64

end

end

/-! ### `Ed448.X86_64.Wnaf.Timing`, which only this module used -/

section

/-! Sparse control flow depends only on the public verification scalars. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64
open VG.Impl.Ed448.Wnaf (digitAt)
open VG.Impl.X448.X86_64 (BITS)
open VG.Proof.Ed448.X86_64.Window (seq_same JointTimingCtx)

structure Ctx (base : Addr) (S K n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  bs : Digits base SDIG S s
  bk : Digits base KDIG K s
  d : E s.mem base 11 = Spec.Ed448.d

theorem Ctx.keep {base : Addr} {S K n : Nat} {s u : State}
    (h : Ctx base S K n s) (hk : Keep base s u)
    (hd : E u.mem base 11 = Spec.Ed448.d) : Ctx base S K n u :=
  ⟨hk.scr h.scr, (hk.gpr _ (by decide)).trans h.rbx,
    h.bs.keep (by decide) (by decide) hk, h.bk.keep (by decide) (by decide) hk, hd⟩

private theorem ctx_agree {base : Addr} {S K n : Nat} {s u : State}
    (h : Ctx base S K n s ∧ Ctx base S K n u) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rbx]) s u := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  · exact h.1.rbx.trans h.2.rbx.symm

def Picked (base : Addr) (S K n : Nat) (d : Int) (s : State) : Prop :=
  Ctx base S K n s ∧ s.gpr .r15 = DigitWord d ∧ s.zf = some (decide (d = 0))

private theorem picked_agree {base : Addr} {S K n : Nat} {d : Int} {s u : State}
    (h : Picked base S K n d s ∧ Picked base S K n d u) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rbx, .r15]) s u := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1.1.scr.rdi.trans h.2.1.scr.rdi.symm
  · exact h.1.1.rbx.trans h.2.1.rbx.symm
  · exact h.1.2.1.trans h.2.2.1.symm

theorem conditional_ct (base : Addr) (S K n o : Nat) (d : Int) (p : Prog isa)
    (ho : o + n + 1 ≤ 8192) (hd : -15 ≤ d ∧ d ≤ 15)
    (hm : ∀ s, Ctx base S K n s → s.mem (off base (o + n)) = CodeByte d)
    (head : RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u)
      (.block (getDigit o)) (fun _ _ => True))
    (hp : RelCT isa (fun s u => Picked base S K n d s ∧ Picked base S K n d u) p (fun _ _ => True)) :
    RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u)
      (.seq (.block (getDigit o)) (.ite .ne p (.block []))) (fun _ _ => True) := by
  have hw (s : State) (h : Ctx base S K n s) : WP isa (.block (getDigit o)) s (Picked base S K n d) := by
    refine WP.mono (getDigit_ok h.scr ho hd h.rbx (hm s h)) fun u ⟨ur, uz, ku⟩ => ?_
    exact ⟨h.keep (keeps_keep (ku.mono (by decide))) (by rw [ku.2.1]; exact h.d), ur, uz⟩
  apply seq_same head hw
  apply RelCT.ite
  · intro s u h
    simp only [eval, h.1.2.2, h.2.2.2, Option.map_some]
  · exact hp.mono (fun _ _ h => h.1) (fun _ _ h => h)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem addBase_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K n : Nat) (hn : n < 461) :
    RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u) (addBase v.bodies) (fun _ _ => True) := by
  apply conditional_ct base S K n SDIG (digitAt S n) _ (by simp only [SDIG]; omega_using [hn])
    (Proof.Ed448.Wnaf.digit_bounds _) (fun _ h => h.bs n hn)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx, .r15])
    (fun _ _ h => picked_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])

theorem addKey_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K n : Nat) (hn : n < 461) :
    RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u) (addKey v.field v.bodies) (fun _ _ => True) := by
  apply conditional_ct base S K n KDIG (digitAt K n) _ (by simp only [KDIG]; omega_using [hn])
    (Proof.Ed448.Wnaf.digit_bounds _) (fun _ h => h.bk n hn)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx, .r15])
    (fun _ _ h => picked_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])

theorem dbl_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K n s) : WP isa v.bodies.dbl s (Ctx base S K n) := by
  refine WP.mono ((FieldVariant.bodies_ok v).dbl h.scr) fun u ⟨ku, eu⟩ => ?_
  exact h.keep ku (by rw [eu, doubleOps_keep _ _ (Or.inl ⟨by decide, by decide⟩), h.d])

theorem base_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K n s) (hn : n < 461) : WP isa (addBase v.bodies) s (Ctx base S K n) := by
  refine WP.mono (addBase_ok (FieldVariant.bodies_ok v) h.scr hn (Proof.Ed448.Wnaf.digit_bounds _)
    h.rbx (h.bs n hn) h.d) fun u ⟨ku, du, _⟩ => h.keep ku du

theorem key_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K n s) (hn : n < 461) : WP isa (addKey v.field v.bodies) s (Ctx base S K n) := by
  refine WP.mono (addKey_ok (FieldVariant.field_ok v) (FieldVariant.bodies_ok v) h.scr hn
    (Proof.Ed448.Wnaf.digit_bounds _) h.rbx (h.bk n hn) h.d) fun u ⟨ku, du, _⟩ => h.keep ku du

theorem dec_ctx {base : Addr} {S K n : Nat} {s : State} (h : Ctx base S K (n + 1) s) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s (Ctx base S K n) := by
  refine WP.mono (dec1_ok s h.rbx) fun u ⟨bu, gu, mu, ru, wu⟩ => ?_
  exact ⟨⟨(gu _ (by decide)).trans h.scr.rdi, wu ▸ h.scr.wr, h.scr.nowrap⟩,
    bu, (by rw [Digits, mu]; exact h.bs), (by rw [Digits, mu]; exact h.bk), (by rw [mu]; exact h.d)⟩

theorem step_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K n : Nat} {s : State}
    (h : Ctx base S K (n + 1) s) (hn : n < 461) : WP isa (step v.field v.bodies) s fun u =>
      Ctx base S K n u ∧ u.zf = some (decide (n = 0)) := by
  refine WP.seq (WP.mono (dec_ctx h) fun a ha => ?_)
  refine WP.seq (WP.mono (dbl_ctx v ha) fun b hb => ?_)
  refine WP.seq (WP.mono (base_ctx v hb hn) fun c hc => ?_)
  refine WP.seq (WP.mono (key_ctx v hc hn) fun d hd => ?_)
  refine WP.mono (testCounter_ok d n hn hd.rbx) fun u ⟨zu, gu, mu, ru, wu⟩ => ?_
  exact ⟨⟨⟨(gu _).trans hd.scr.rdi, wu ▸ hd.scr.wr, hd.scr.nowrap⟩, (gu _).trans hd.rbx,
    (by rw [Digits, mu]; exact hd.bs), (by rw [Digits, mu]; exact hd.bk), (by rw [mu]; exact hd.d)⟩, zu⟩

theorem step_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K n : Nat) (hn : n < 461) :
    RelCT isa (fun s u => Ctx base S K (n + 1) s ∧ Ctx base S K (n + 1) u)
      (step v.field v.bodies) (fun _ _ => True) := by
  have dbl : RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u) v.bodies.dbl (fun _ _ => True) := by
    cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx])
      (fun _ _ h => ctx_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  have test : RelCT isa (fun s u => Ctx base S K n s ∧ Ctx base S K n u)
      (.block [.alu .test .rbx (.reg .rbx)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  apply seq_same (p := .block [.alu .sub .rbx (.imm 1)]) _ (fun _ h => dec_ctx h)
    (seq_same dbl (fun _ h => dbl_ctx v h)
      (seq_same (addBase_ct v base S K n hn) (fun _ h => base_ctx v h hn)
        (seq_same (addKey_ct v base S K n hn) (fun _ h => key_ctx v h hn) test)))
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)

theorem loop_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat) :
    RelCT isa (fun s u => Ctx base S K 461 s ∧ Ctx base S K 461 u)
      (.loop (step v.field v.bodies) .ne) (fun _ _ => True) := by
  let I (n : Nat) (s u : State) := 1 ≤ n ∧ n ≤ 461 ∧ Ctx base S K n s ∧ Ctx base S K n u
  have hstep : ∀ n, RelCT isa (I n) (step v.field v.bodies) fun s u =>
      isa.eval .ne s = isa.eval .ne u ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m < n, I m s u) := by
    intro n s u tr1 tr2 s' u' hn ex1 ex2
    obtain ⟨hn0, hn1, hs, hu⟩ := hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hn0]⟩
    obtain ⟨he, _⟩ := step_ct v base S K m (by omega_using [hn1]) s u tr1 tr2 s' u' ⟨hs, hu⟩ ex1 ex2
    obtain ⟨_, a, ea, ha⟩ := step_ctx v hs (by omega_using [hn1])
    obtain ⟨_, b, eb, hb⟩ := step_ctx v hu (by omega_using [hn1])
    obtain ⟨_, rfl⟩ := Exec.det ex1 ea
    obtain ⟨_, rfl⟩ := Exec.det ex2 eb
    have za : isa.eval .ne s' = some (!decide (m = 0)) := by simp only [eval, ha.2, Option.map_some]
    have zb : isa.eval .ne u' = some (!decide (m = 0)) := by simp only [eval, hb.2, Option.map_some]
    refine ⟨he, za.trans zb.symm, fun _ => trivial, fun hz => ?_⟩
    have hp : 0 < m := by rw [za] at hz; simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hz; omega_using [hz]
    exact ⟨m, by omega_using [], hp, by omega_using [hn1], ha.1, hb.1⟩
  exact (RelCT.loop I hstep 461).mono (fun _ _ h => ⟨by decide, by decide, h⟩) (fun _ _ h => h)

def jointHead (v : Impl.Ed448.X86_64.FieldVariant) : Prog isa :=
  .seq (.seq (.seq (Window.table v.bodies) (recode BITS SDIG)) (recode KBITS KDIG))
    (.block (constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ [.mov32 .rbx (.imm 461)]))

theorem jointHead_ok (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K : Nat} {s : State}
    (h : JointTimingCtx base S K s) (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    WP isa (jointHead v) s (Ctx base S K 461) := by
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (WP.mono (Window.table_ok (FieldVariant.bodies_ok v) h.scr h.d h.z h.p)
    fun a ⟨ka, da, _⟩ => ?_)
  have bsA := h.bs.keepW (by decide) (by decide) ka
  have bkA := h.bk.keepW (by decide) (by decide) ka
  refine WP.seq (WP.mono (recode_ok (ka.scr h.scr) (by decide) (by decide) (by decide) bsA hS)
    fun b hB => ?_)
  have bkB : Window.Bits base KBITS K b := by
    intro i hi
    rw [hB.mem _ (Or.inl (by rw [ofs_off' base (by simp only [KBITS]; omega_using [hi])]; simp only [KBITS, SDIG]; omega_using [hi]))]
    exact bkA i hi
  refine WP.seq (WP.mono (recode_ok hB.scr (by decide) (by decide) (by decide) bkB hK) fun c hC => ?_)
  have sb : Digits base SDIG S b := hB.digits
  have sc : Digits base SDIG S c := by
    intro i hi
    rw [hC.mem _ (Or.inl (by rw [ofs_off' base (by simp only [SDIG]; omega_using [hi])]; simp only [SDIG, KDIG]; omega_using [hi]))]
    exact sb i hi
  have kc : Digits base KDIG K c := hC.digits
  refine WP.mono (initPoint_ok hC.scr) fun d hD => ?_
  refine ⟨hD.scr, hD.rbx, ?_, ?_, ?_⟩
  · intro i hi
    rw [hD.mem _ (Or.inr (by rw [ofs_off' base (by simp only [SDIG]; omega_using [hi])]; simp only [SDIG]; omega_using []))]
    exact sc i hi
  · intro i hi
    rw [hD.mem _ (Or.inr (by rw [ofs_off' base (by simp only [KDIG]; omega_using [hi])]; simp only [KDIG]; omega_using []))]
    exact kc i hi
  · rw [hD.d, hC.env (by decide), hB.env (by decide)]; exact da

theorem joint_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat)
    (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    RelCT isa (fun s u => JointTimingCtx base S K s ∧ JointTimingCtx base S K u)
      (joint v.field v.bodies KBITS) (fun _ _ => True) := by
  have head : RelCT isa (fun s u => JointTimingCtx base S K s ∧ JointTimingCtx base S K u)
      (jointHead v) (fun _ _ => True) := by
    cases v <;> apply relCT_sum (Taint.ofRegs [.rdi]) _ (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
    all_goals
      intro s u h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  exact (seq_same head (fun _ h => jointHead_ok v h hS hK) (loop_ct v base S K)).assoc.assoc.assoc

end VG.Proof.Ed448.X86_64.Wnaf

end

end

/-!
# Ed448 verification's equation on x86-64: `Verified`

Correctness and ABI preservation for both field backends, together with a
relational timing proof. Decoding uses fixed addresses. The joint multiplication
indexes its projective table using public challenge digits, whose values follow
from correctness of scalar decoding. The reviewed contract already makes every
verification input public; no signing or secret-scalar contract changes.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64
set_option exponentiation.threshold 1024

open VG VG.X86_64 VG.Impl.Ed448.X86_64

/-- The arguments are public; the working space is writable region 0, at `rcx`. -/
def verifyEquationτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [8192], bases := [(.rcx, 0, 0)] }

theorem verifyEquation_agree {s₁ s₂ : State} (h₁ : verifyEquationLocal.pre s₁)
    (h₂ : verifyEquationLocal.pre s₂) (hpub : verifyEquationLocal.pub s₁ s₂) :
    X86_64.Taint.Agree verifyEquationτ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, _, _⟩ := hpub
  have wf : ∀ s, verifyEquationLocal.pre s → X86_64.Taint.Wf verifyEquationτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, verifyEquationτ], by simp [hw], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [verifyEquationτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [verifyEquationτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [p1, p2, p3, p4, p0]
  · rw [h₁.2.1, h₂.2.1, p4]
  · intro sl h; simp [verifyEquationτ] at h
  · intro sl h; simp [verifyEquationτ] at h

/-- The postcondition reads registers only. -/
theorem verifyEquation_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (_ : verifyEquationLocal.pre s)
    (_ : Clear (hole (s.gpr .rsp)) s) (hp : verifyEquationLocal.post s b) :
    verifyEquationLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := hp

/-! ## Public-input timing, with decoding summaries -/

/-- What the code needs public after the entry, and the registers `rs` (the
encoding's address `rsi`, for the decoding). -/
def verifySumτ (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi, .rsp]), flags := false, lens := [8192], bases := [(.rdi, 0, 0)],
    slots := [(0, PPK, 8), (0, PSIG, 8), (0, PCUR, 8), (0, CNT, 8)] }

taint_summary verifyRootInlineSum : taintS (verifySumτ [])
    (rootCallFor .scalar).inline
taint_summary verifyDecodeInlineSum : taintS (verifySumτ [.rsi])
    (decode Impl.X448.X86_64.baseline 6 7 (rootCallFor .scalar).inline) using verifyRootInlineSum
taint_summary verifyRootAdxInlineSum : taintS (verifySumτ [])
    (rootCallFor .adx).inline
taint_summary verifyDecodeAdxInlineSum : taintS (verifySumτ [.rsi])
    (decode Impl.X448.X86_64.adx 6 7 (rootCallFor .adx).inline) using verifyRootAdxInlineSum

theorem verifyPrefix_ct (v : Impl.Ed448.X86_64.FieldVariant) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub
      (verifyPrefix v.field (rootCallFor v).inline) := by
  cases v
  · obtain ⟨_, hc⟩ : ∃ h, (taintS.check verifyEquationτ
        (verifyPrefix Impl.X448.X86_64.baseline (rootCallFor .scalar).inline) h).isSome = true := by
      taint_decide_sum [verifyDecodeInlineSum]
    exact VG.Taint.constantTime (A := taintS) verifyEquationτ
      (fun _ _ h₁ h₂ hp => verifyEquation_agree h₁ h₂ hp) hc
  · obtain ⟨_, hc⟩ : ∃ h, (taintS.check verifyEquationτ
        (verifyPrefix Impl.X448.X86_64.adx (rootCallFor .adx).inline) h).isSome = true := by
      taint_decide_sum [verifyDecodeAdxInlineSum]
    exact VG.Taint.constantTime (A := taintS) verifyEquationτ
      (fun _ _ h₁ h₂ hp => verifyEquation_agree h₁ h₂ hp) hc

theorem verifyFinish_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) :
    RelCT isa (fun s u => s.gpr .rdi = base ∧ u.gpr .rdi = base)
      (vfinish v.field v.bodies) (fun _ _ => True) := by
  cases v <;> apply relCT_sum (Taint.ofRegs [.rdi]) _ (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  all_goals
    intro s u h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact h.1.trans h.2.symm

theorem verifyRest_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat)
    (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    RelCT isa (fun s u => Window.JointTimingCtx base S K s ∧ Window.JointTimingCtx base S K u)
      (.seq (Wnaf.joint v.field v.bodies KBITS) (vfinish v.field v.bodies)) (fun _ _ => True) := by
  apply Window.seq_same (Wnaf.joint_ct v base S K hS hK) _ (verifyFinish_ct v base)
  intro s h
  exact WP.mono (Wnaf.joint_ok (FieldVariant.field_ok v) (FieldVariant.bodies_ok v)
    h.scr (by decide) (by decide) h.bs h.bk hS hK h.d h.z h.p) fun u hu => hu.1.rdi

theorem signatureScalar_below (s : State) : signatureScalar s < 2 ^ 456 := by
  exact decodeLE_below (bytesAt57_len s.mem (s.gpr .rsi + BitVec.ofNat 64 57))

theorem challengeScalar_below (s : State) : challengeScalar s < 2 ^ 456 := by
  exact decodeLE_below (bytesAt57_len s.mem (s.gpr .rdx))

theorem verifyEquationFor_ctI (v : Impl.Ed448.X86_64.FieldVariant) (hR : Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub (verifyEquationFor v).inline := by
  let P (s u : State) := verifyEquationLocal.pre s ∧ verifyEquationLocal.pre u ∧ verifyEquationLocal.pub s u
  have head : RelCT isa P (verifyPrefix v.field (rootCallFor v).inline) (fun _ _ => True) :=
    fun s u t1 t2 s' u' h e1 e2 => ⟨verifyPrefix_ct v s u t1 t2 s' u' h.1 h.2.1 h.2.2 e1 e2, trivial⟩
  have hw := head.wpDep (F := fun (s u : State) =>
      Window.JointTimingCtx (s.gpr .rcx) (signatureScalar s) (challengeScalar s) u)
    (fun s u h => ⟨verifyPrefix_ok (FieldVariant.field_ok v) hR (rootCallFor_ok v) h.1,
      verifyPrefix_ok (FieldVariant.field_ok v) hR (rootCallFor_ok v) h.2.1⟩)
  have hh := hw.seq (Q := fun _ _ => True) (by
    intro s u t1 t2 s' u' h e1 e2
    obtain ⟨_, a, b, hab, ha, hb⟩ := h
    obtain ⟨_, _, _, _, base, sig, chal⟩ := hab.2.2
    rw [← base, ← sig, ← chal] at hb
    have hS := signatureScalar_below a
    have hK := challengeScalar_below a
    exact verifyRest_ct v (a.gpr .rcx) (signatureScalar a) (challengeScalar a) hS hK
      s u t1 t2 s' u' ⟨ha, hb⟩ e1 e2)
  have result := hh.assoc.assoc.assoc.assoc
  rw [verifyEquationFor_inline]
  exact result.constantTime

end VG.Proof.Ed448.X86_64
