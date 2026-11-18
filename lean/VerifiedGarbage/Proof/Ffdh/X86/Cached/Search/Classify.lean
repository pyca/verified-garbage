module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.AttemptVerified
import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Ffdh.X86.Entry

/-! ### `Ffdh.X86.Cached.Search.Call`, which this module and modules that import it used -/

section

/-! # The attempt's call (x86)

`vg_ffdh_generate_key`, called with its arguments in the frame, returns the
status of the attempt on the tape's next `p_len` octets and writes its
outputs, changing memory only at the outputs, the working space and the
stack the controller uses (`call_ok`).
-/

@[expose] public section

/-! ## The attempt's precondition (x86)

With its eleven arguments in the frame (`ArgsAt`), `vg_ffdh_generate_key`'s
contract holds on its entry, narrowed to the domain and the tape's next
`p_len` octets, which it reads, and to the outputs, the working space and
its frame of arguments, which it writes (`call_pre`).
-/

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The tape's next `p_len` octets. -/
abbrev winR (o : State) (used : Nat) : Region := ⟨(arg o 8 + BitVec.ofNat 32 used).setWidth 64, (arg o 7).toNat⟩

/-- What the callee may read and write. -/
abbrev callRd (o : State) (used : Nat) : List Region := [dR o, winR o used, cR o]
abbrev callWr (o : State) : List Region :=
  [⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩, ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩, bR o, frR o]

/-- The callee's arguments, on its entry. -/
theorem ce_arg {o t : State} {used : Nat} (A : KeySearchABI o)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 13 t.mem)
    (rd wr : List Region) {j : Nat} (hj : j < 13) :
    arg (t.callEntry.withRegions rd wr) j = callArg o used j := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  obtain hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 52 := by rw [he]; exact VG.X86.sub_toNat (by unfold argsBytes; omega_using [h1])
  rw [arg_withRegions, arg_callEntry (by omega_using [h1, hn]) (by omega_using [hj, hn]), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    addr_sub A (by decide) (by unfold argsBytes; omega_using [hj])]
  rfl

/-- The window's base, at its offset in the tape. -/
theorem win_base {o : State} (A : KeySearchABI o) {used : Nat} (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) :
    (arg o 8 + BitVec.ofNat 32 used).setWidth 64 = argumentPointer o 8 + BitVec.ofNat 64 used := by
  have := A.rBound
  have := A.pLen
  unfold Spec.Ffdh.pLenValid at this
  exact addr_eq (by omega_arith)

theorem win_toNat {o : State} (A : KeySearchABI o) {used : Nat} (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) :
    (arg o 8 + BitVec.ofNat 32 used).toNat = (arg o 8).toNat + used := by
  have := A.rBound
  have := A.pLen
  unfold Spec.Ffdh.pLenValid at this
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega_using [hu])]
  exact Nat.mod_eq_of_lt (by omega_arith)

theorem win_sub {o : State} (A : KeySearchABI o) {used : Nat} (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) :
    Region.Sub (winR o used) (rR o) := by
  rw [winR, win_base A hu]; exact Offset.sub_base _ hu

/-- The callee's stack pointer on its entry. -/
theorem esp_sub4 {o t : State} (A : KeySearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 56 := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  rw [he]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, argsBytes]
  have := (o.gpr .esp).isLt
  show (2 ^ 32 - 4 % 2 ^ 32 + (2 ^ 32 - 52 % 2 ^ 32 + (o.gpr .esp).toNat) % 2 ^ 32) % 2 ^ 32 = _
  omega_using []

/-- The domain and the context lie apart from every region the run may write. -/
theorem frameR_apart {o : State} (A : KeySearchABI o) {R : Region} (hx : R.Disjoint (xR o)) (hy : R.Disjoint (yR o))
    (hu : R.Disjoint (uR o)) (hb : R.Disjoint (bR o)) (hs : R.Disjoint (sR o)) (ha : R.Disjoint (aR o))
    (hl : R.Disjoint (lowR o)) : ∀ r ∈ frameR o, R.Disjoint r := by
  intro r hr
  rw [frameR, A.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hx, hy, hu, hb, hs, ha, hl]

/-- The domain, through the run's writes. -/
theorem dom_frame {o : State} (A : KeySearchABI o) {m : Mem} (F : Frame (frameR o) o.mem m) :
    Spec.Rsa.bytesAt m (argumentPointer o 5) (arg o 6).toNat =
      Spec.Rsa.bytesAt o.mem (argumentPointer o 5) (arg o 6).toNat :=
  bytes_frame F (frameR_apart A A.xd.symm A.yd.symm A.ud.symm A.db A.ds A.da A.lowD.symm)
    (by have := A.dBound; omega_using [])

/-- The context, through the run's writes. -/
theorem ctx_frame {o : State} (A : KeySearchABI o) {m : Mem} (F : Frame (frameR o) o.mem m) :
    Spec.Rsa.wordsAt m (argumentPointer o 13) (arg o 14).toNat =
      Spec.Rsa.wordsAt o.mem (argumentPointer o 13) (arg o 14).toNat := by
  have cB := A.cBound
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => ?_
  obtain hi' := List.mem_range.mp hi
  exact F.readW (r := cR o) (Offset.contains_base _ (by omega_using [hi']) (by omega_using [hi']))
    (frameR_apart A A.xc.symm A.yc.symm A.uc.symm A.bc.symm A.sc.symm A.ca A.lowC.symm) (by decide)

theorem call_pre {o t : State} {used : Nat} (A : KeySearchABI o) (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 13 t.mem)
    (F : Frame (frameR o) o.mem t.mem) :
    (Proof.Ffdh.cachedGenerateKeyContract abi Proof.Ffdh.X86.stack).pre
      (t.callEntry.withRegions (callRd o used) (callWr o)) := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  obtain hs4 := esp_sub4 A he
  obtain hs4n : (o.gpr .esp - BitVec.ofNat 32 56).toNat = (o.gpr .esp).toNat - 56 := VG.X86.sub_toNat (by omega_using [h1])
  obtain ha0 : argAddr (t.callEntry.withRegions (callRd o used) (callWr o)) 0 = low o + BitVec.ofNat 64 176 := by
    rw [argAddr_withRegions, argAddr_callEntry, show 4 * 0 = 0 from rfl, BitVec.add_zero, he,
      sw_sub A (by decide)]; rfl
  obtain hl116 : (o.gpr .esp - BitVec.ofNat 32 56).setWidth 64 - 172#64 = low o := by
    rw [sw_sub A (by decide)]; show low o + BitVec.ofNat 64 172 - BitVec.ofNat 64 172 = _
    exact BitVec.add_sub_cancel _ _
  obtain xr := xR_eq A
  obtain yr := yR_eq A
  obtain W := win_sub A hu
  obtain Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  obtain Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  obtain Bs : Region.Sub ⟨low o, 172⟩ (lowR o) := Region.sub_prefix (by decide)
  obtain dXY : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xr, ← yr]; exact A.xy
  obtain dXD : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (dR o) := by rw [← xr]; exact A.xd
  obtain dXW : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (winR o used) := by
    rw [← xr]; exact A.xr.sub_right W
  obtain dXB : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (bR o) := by rw [← xr]; exact A.xb
  obtain dXF : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (frR o) := by
    rw [← xr]; exact A.lowX.symm.sub_right Fs
  obtain dYD : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (dR o) := by rw [← yr]; exact A.yd
  obtain dYW : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (winR o used) := by
    rw [← yr]; exact A.yr.sub_right W
  obtain dYB : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (bR o) := by rw [← yr]; exact A.yb
  obtain dYF : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (frR o) := by
    rw [← yr]; exact A.lowY.symm.sub_right Fs
  have dDB : Region.Disjoint (dR o) (bR o) := A.db
  obtain dDF : Region.Disjoint (dR o) (frR o) := A.lowD.symm.sub_right Fs
  obtain dWB : Region.Disjoint (winR o used) (bR o) := A.rb.sub_left W
  obtain dWF : Region.Disjoint (winR o used) (frR o) := (A.lowRand.symm.sub_left W).sub_right Fs
  obtain dBF : Region.Disjoint (bR o) (frR o) := A.lowB.symm.sub_right Fs
  obtain rX : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xr]; exact A.lowX.sub_left Rs
  obtain rY : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yr]; exact A.lowY.sub_left Rs
  obtain rD : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (dR o) := A.lowD.sub_left Rs
  obtain rW : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (winR o used) := (A.lowRand.sub_left Rs).sub_right W
  obtain rB : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (bR o) := A.lowB.sub_left Rs
  obtain rF : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (frR o) :=
    Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain bX : Region.Disjoint ⟨low o, 172⟩ ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xr]; exact A.lowX.sub_left Bs
  obtain bY : Region.Disjoint ⟨low o, 172⟩ ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yr]; exact A.lowY.sub_left Bs
  obtain bD : Region.Disjoint ⟨low o, 172⟩ (dR o) := A.lowD.sub_left Bs
  obtain bW : Region.Disjoint ⟨low o, 172⟩ (winR o used) := (A.lowRand.sub_left Bs).sub_right W
  obtain bB : Region.Disjoint ⟨low o, 172⟩ (bR o) := A.lowB.sub_left Bs
  obtain bF : Region.Disjoint ⟨low o, 172⟩ (frR o) := Offset.base_disjoint _ (by omega_using []) (by omega_using [])
  obtain xB : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  obtain yB : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  obtain wB : (arg o 8 + BitVec.ofNat 32 used).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by
    rw [win_toNat A hu]; have := A.rBound; omega_using [hu, this]
  obtain cX : Region.Disjoint (cR o) ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by rw [← xr]; exact A.xc.symm
  obtain cY : Region.Disjoint (cR o) ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by rw [← yr]; exact A.yc.symm
  have cB' : Region.Disjoint (cR o) (bR o) := A.bc.symm
  obtain cF : Region.Disjoint (cR o) (frR o) := A.lowC.symm.sub_right Fs
  obtain rC : Region.Disjoint ⟨low o + BitVec.ofNat 64 172, 4⟩ (cR o) := A.lowC.sub_left Rs
  obtain bC : Region.Disjoint ⟨low o, 172⟩ (cR o) := A.lowC.sub_left Bs
  have cBd := A.cBound
  have cL := A.ctxLen
  obtain Fv : ∀ v : BitVec 32, Frame (frameR o) o.mem (t.mem.writeW (low o + 172#64) v) := fun v =>
    F.writeW (List.mem_append_right _ (List.mem_singleton_self _)) v (low_contains A (d := 172) (n := 4) (by decide))
  obtain dv : ∀ v : BitVec 32, Spec.Ffdh.domainValid (arg o 7).toNat
      (Spec.Rsa.bytesAt (t.mem.writeW (low o + 172#64) v) (argumentPointer o 5) (arg o 6).toNat) = true := fun v => by
    rw [dom_frame A (Fv v)]; exact A.domValid
  obtain cg : ∀ v : BitVec 32, Spec.Ffdh.generationPrecompute (arg o 7).toNat
      (Spec.Rsa.bytesAt (t.mem.writeW (low o + 172#64) v) (argumentPointer o 5) (arg o 6).toNat) =
        some (Spec.Rsa.wordsAt (t.mem.writeW (low o + 172#64) v) (argumentPointer o 13) (arg o 14).toNat) := fun v => by
    rw [dom_frame A (Fv v), ctx_frame A (Fv v)]; exact A.ctx
  have dB := A.dBound
  have sB := A.bBound
  have pL := A.pLen
  have dL := A.dLen
  have sL := A.scratchLength
  obtain st : Proof.Ffdh.X86.stack ≤ (o.gpr .esp - BitVec.ofNat 32 56).toNat := by
    rw [hs4n]; show 172 ≤ _; omega_using [h1]
  obtain st' : (o.gpr .esp - BitVec.ofNat 32 56).toNat + 4 + 52 ≤ 2 ^ 32 := by rw [hs4n]; omega_using []
  sig_pre [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes, stackBelow, Spec.Ffdh.generationContextAt]
  simp only [hs4, ha0, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceIte, BitVec.add_sub_cancel, ce_arg A he ha _ _ (show 0 < 13 by decide), ce_arg A he ha _ _ (show 1 < 13 by decide),
    ce_arg A he ha _ _ (show 2 < 13 by decide), ce_arg A he ha _ _ (show 3 < 13 by decide),
    ce_arg A he ha _ _ (show 4 < 13 by decide), ce_arg A he ha _ _ (show 5 < 13 by decide),
    ce_arg A he ha _ _ (show 6 < 13 by decide), ce_arg A he ha _ _ (show 7 < 13 by decide),
    ce_arg A he ha _ _ (show 8 < 13 by decide), ce_arg A he ha _ _ (show 9 < 13 by decide),
    ce_arg A he ha _ _ (show 10 < 13 by decide), ce_arg A he ha _ _ (show 11 < 13 by decide),
    ce_arg A he ha _ _ (show 12 < 13 by decide), callArg, sw_sub A (show 56 ≤ 228 by decide)]
  sig_and_intros
  all_goals first
    | exact True.intro
    | exact dv _
    | exact cg _
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

end VG.Proof.Ffdh.X86.Cached.Search

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (argumentPointer)

theorem callee_stack : stackUse Impl.Ffdh.X86.Cached.Generate.code = 172 := by rsa_stack_use

/-- No instruction of the callee writes `esp`: proved once, for `body_noSp` too. -/
private theorem callee_all :
    Impl.Ffdh.X86.Cached.Generate.code.allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

theorem callee_noSp : NoSp Impl.Ffdh.X86.Cached.Generate.code := NoSp.of_all callee_all

/-- The bytes `[u, u + l)` of `n` at `p`. -/
theorem bytes_window (m : Mem) (p : Addr) {u l n : Nat} (h : u + l ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 u) l = ((Spec.Rsa.bytesAt m p n).drop u).take l := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_using [h])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What an attempt leaves at the outputs. -/
def AttemptOut (o : State) (used : Nat) (m : Mem) : Prop :=
  let a := (ofState o).a
  let x := vettedScalarOfOctets a (((randOf o).drop used).take (arg o 7).toNat)
  if keyStatus a x = 1 then
    Spec.Rsa.bytesAt m (argumentPointer o 0) (arg o 7).toNat = Spec.Rsa.i2osp x (arg o 7).toNat ∧
      Spec.Rsa.bytesAt m (argumentPointer o 2) (arg o 7).toNat =
        Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (arg o 7).toNat
  else Spec.Rsa.bytesAt m (argumentPointer o 0) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
    Spec.Rsa.bytesAt m (argumentPointer o 2) (arg o 7).toNat = List.replicate (arg o 7).toNat 0

theorem call_covers {o t : State} {used : Nat} (A : KeySearchABI o) (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat)
    (hrd : t.rd = o.rd) (hwr : t.wr = frR o :: o.wr) :
    Covers (callRd o used ++ callWr o) (t.rd ++ t.wr) ∧ Covers (callWr o) t.wr := by
  have xL := A.xLen
  have yL := A.yLen
  obtain hw : ∀ r ∈ callWr o, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
    intro r hr
    rw [hwr, A.wr]
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨xR o, by simp, 0, (BitVec.add_zero _).symm, by simp [xL]⟩
    · exact ⟨yR o, by simp, 0, (BitVec.add_zero _).symm, by simp [yL]⟩
    · exact ⟨bR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨frR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [hrd, A.rd]
    simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨rR o, by simp, used, win_base A hu, hu⟩
    · exact ⟨cR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', off, hb⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', off, hb⟩

/-- A region apart from every region the run may write. -/
theorem apart {o : State} (A : KeySearchABI o) {R : Region} (hx : R.Disjoint (xR o)) (hy : R.Disjoint (yR o))
    (hu : R.Disjoint (uR o)) (hb : R.Disjoint (bR o)) (hs : R.Disjoint (sR o)) (ha : R.Disjoint (aR o))
    (hl : R.Disjoint (lowR o)) : ∀ r ∈ frameR o, R.Disjoint r := by
  intro r hr
  rw [frameR, A.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hx, hy, hu, hb, hs, ha, hl]

/-- The domain, through the run's writes. -/
theorem dom_apart {o : State} (A : KeySearchABI o) : ∀ r ∈ frameR o, (dR o).Disjoint r :=
  apart A A.xd.symm A.yd.symm A.ud.symm A.db A.ds A.da A.lowD.symm

/-- The tape, through the run's writes. -/
theorem rand_apart {o : State} (A : KeySearchABI o) : ∀ r ∈ frameR o, (rR o).Disjoint r :=
  apart A A.xr.symm A.yr.symm A.ur.symm A.rb A.rs A.ra A.lowRand.symm

/-- The call's return address. -/
theorem ret_eq {o t : State} (A : KeySearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 172 := by
  rw [esp_sub4 A he, sw_sub A (by decide)]

/-- The stack below the call. -/
theorem below_eq {o t : State} (A : KeySearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    below (t.gpr .esp) (stackUse Impl.Ffdh.X86.Cached.Generate.code + 4) = ⟨low o, 176⟩ := by
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  obtain hl := low_toNat A
  have := (o.gpr .esp).isLt
  obtain e : (o.gpr .esp - BitVec.ofNat 32 argsBytes - BitVec.ofNat 32 (172 + 4)).setWidth 64 = low o := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, hl, argsBytes]
    omega_using [h1]
  rw [callee_stack, below, he, e]

theorem keyStatus_le3 (a : Parameters) (x : Nat) : keyStatus a x ≤ 3 := by
  rcases keyStatus_cases a x with h | h | h <;> rw [h] <;> decide

/-- The callee's domain and tape, on its entry. -/
theorem entry_bytes {o t : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f t)
    (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) (v : BitVec 32) :
    Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v) (argumentPointer o 5) (arg o 6).toNat =
      (ofState o).dom ∧
    Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v) ((arg o 8 + BitVec.ofNat 32 used).setWidth 64)
      (arg o 7).toNat = ((randOf o).drop used).take (arg o 7).toNat := by
  have A := h.abi
  have hpl := A.pLen
  unfold Spec.Ffdh.pLenValid at hpl
  have hb := A.dBound
  have hrb := A.rBound
  obtain fe : ∀ v : BitVec 32, Frame [⟨low o + BitVec.ofNat 64 172, 4⟩] t.mem
      (t.mem.writeW (low o + BitVec.ofNat 64 172) v) := fun v =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  obtain dE : ∀ v : BitVec 32, Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v) (argumentPointer o 5)
      (arg o 6).toNat = (ofState o).dom := fun v => by
    rw [bytes_frame (fe v) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.lowD.sub_left Rs).symm) (by omega_using []),
      bytes_frame h.frame (dom_apart A) (by omega_using [])]; rfl
  obtain rE : ∀ v : BitVec 32, Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v)
      ((arg o 8 + BitVec.ofNat 32 used).setWidth 64) (arg o 7).toNat =
      ((randOf o).drop used).take (arg o 7).toNat := fun v => by
    obtain W := win_sub A hu
    rw [bytes_frame (fe v) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ((A.lowRand.sub_left Rs).sub_right W).symm)
      (by omega_using []), bytes_frame h.frame (fun r hr => (rand_apart A r hr).sub_left W) (by omega_using []),
      win_base A hu, bytes_window _ _ hu]
  exact ⟨dE v, rE v⟩

theorem call_ok {o t : State} {e : BitVec 32} {used keys scalars : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used keys scalars) t)
    (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) (ha : ArgsAt o used 13 t.mem) :
    WP isa (.call "vg_ffdh_generate_key_cached" Impl.Ffdh.X86.Cached.Generate.code) t fun u =>
      Fr o liveDs (liveF (ofState o) e used keys scalars) u ∧
      u.gpr .eax = BitVec.ofNat 32 (attemptStatus .cached (ofState o).a (arg o 7).toNat ((randOf o).drop used)) ∧
      AttemptOut o used u.mem := by
  have A := h.abi
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  obtain hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 52 := by
    rw [h.esp]; exact VG.X86.sub_toNat (by unfold argsBytes; omega_using [h1])
  obtain ⟨hc, hcw⟩ := call_covers (t := t) A hu h.rd h.wr
  refine WP.call Proof.Ffdh.X86.Cached.verified.1 callee_noSp (by rw [callee_stack, hn]; omega_using [h1])
    (call_pre A hu h.esp ha h.frame) hc hcw fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  have hp := hpost
  sig_post [Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes] at hp
  simp only [ce_arg A h.esp ha _ _ (show 0 < 13 by decide),
    ce_arg A h.esp ha _ _ (show 2 < 13 by decide), ce_arg A h.esp ha _ _ (show 4 < 13 by decide), ce_arg A h.esp ha _ _ (show 5 < 13 by decide),
    ce_arg A h.esp ha _ _ (show 6 < 13 by decide), ce_arg A h.esp ha _ _ (show 7 < 13 by decide),
    ce_arg A h.esp ha _ _ (show 8 < 13 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, ret_eq A h.esp] at hp
  have hpl := A.pLen
  unfold Spec.Ffdh.pLenValid at hpl
  obtain dE := fun v => (entry_bytes h hu v).1
  obtain rE := fun v => (entry_bytes h hu v).2
  simp only [dE, rE] at hp
  obtain ⟨hr, hout⟩ := hp
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  have hS := A.sBound
  obtain hA : Aligned liveDs := by decide
  obtain Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  obtain xr := xR_eq A
  obtain yr := yR_eq A
  obtain fr : Frame (frameR o) t.mem u.mem := hf.sub fun r hr => by
    rw [below_eq A h.esp] at hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨xR o, List.mem_append_left _ (by rw [A.wr]; simp), by rw [xr]; exact fun _ h => h⟩
    · exact ⟨yR o, List.mem_append_left _ (by rw [A.wr]; simp), by rw [yr]; exact fun _ h => h⟩
    · exact ⟨bR o, List.mem_append_left _ (by rw [A.wr]; simp), fun _ h => h⟩
    · exact ⟨lowR o, List.mem_append_right _ (List.mem_singleton_self _), Fs⟩
    · exact ⟨lowR o, List.mem_append_right _ (List.mem_singleton_self _), Region.sub_prefix (by decide)⟩
  refine ⟨⟨A, hrd.trans h.rd, hwr.trans h.wr, by rw [hcs .esp (by decide), h.esp],
    by rw [hcs .esi (by decide), h.esi], fun r hr hne hsp => by rw [hcs r hr, h.saved r hr hne hsp],
    h.frame.trans fr, h.words.frame hS hA hf fun r hr => ?_⟩, ?_, ?_⟩
  · rw [below_eq A h.esp] at hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [← xr]; exact A.xs.symm
    · rw [← yr]; exact A.ys.symm
    · exact A.bs.symm
    · exact A.lowS.symm.sub_right Fs
    · exact A.lowS.symm.sub_right (Region.sub_prefix (by decide))
  · apply BitVec.eq_of_toNat_eq
    rw [hr, attemptStatus, toNat_ofNat_lt (Nat.lt_of_le_of_lt (keyStatus_le3 _ _) (by decide))]
    rfl
  · rw [← hm₂]; exact hout

theorem body_noSp :
    NoSp (Code.seq (.block arguments) (.call "vg_ffdh_generate_key_cached" Impl.Ffdh.X86.Cached.Generate.code) :
      Prog isa) := NoSp.of_all (by rsa_stack_shape [callee_all])

/-- Back from the frame. -/
theorem Fr.free {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : Fr o ds f s) :
    St o ds f (freed argsBytes s) := by
  refine ⟨h.abi, h.rd, by rw [freed_wr, h.wr]; rfl, ?_, by rw [freed_gpr _ _ (by decide), h.esi],
    fun r hr hne => ?_, h.frame, h.words⟩
  · rw [freed_esp, h.esp, BitVec.sub_add_cancel]
  · by_cases hsp : r = .esp
    · subst hsp; rw [freed_esp, h.esp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ hsp, h.saved r hr hne hsp]

theorem attempt_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s)
    (hu : used + p.len ≤ p.randLen) :
    WP isa attempt s fun u => St o liveDs (liveF p (o.gpr .esi) used keys scalars) u ∧
      u.gpr .eax = BitVec.ofNat 32 (attemptStatus .cached p.a p.len ((randOf o).drop used)) ∧ AttemptOut o used u.mem := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have h1 : 228 ≤ (o.gpr .esp).toNat := A.stackLow
  refine WP.frameAllocLocal (by decide) (by decide) (by decide) (by rw [S.esp]; unfold argsBytes; omega_using [h1])
    body_noSp (fun t m u ⟨St', e, out⟩ fl => ?_) ?_
  · -- What the attempt leaves lies apart from its frame.
    have hS := A.sBound
    obtain fl' : Frame [lowR o] t.mem m := fl.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [S.esp]
      show Region.Sub ⟨(o.gpr .esp - BitVec.ofNat 32 argsBytes).setWidth 64, argsBytes⟩ _
      rw [sw_sub A (by decide)]; exact low_sub (by decide)
    obtain hx := VG.Proof.Rsa.rsa_bytes_frame fl' (src := argumentPointer o 0) (k := (arg o 7).toNat)
      (by have := (arg o 7).isLt; omega_arith) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← A.xLen]; exact A.lowX.symm
    obtain hy := VG.Proof.Rsa.rsa_bytes_frame fl' (src := argumentPointer o 2) (k := (arg o 7).toNat)
      (by have := (arg o 7).isLt; omega_arith) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← A.yLen]; exact A.lowY.symm
    refine ⟨⟨St'.abi, St'.rd, St'.wr, St'.esp, St'.esi, St'.saved,
      St'.frame.trans (fl'.mono fun r hr => ?_), St'.words.frame hS (by decide) fl' fun r hr => ?_⟩, e, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.lowS.symm
    · show AttemptOut o used m
      simpa only [AttemptOut, hx, hy] using out
  · refine WP.seq (WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ?_)
    exact WP.mono (call_ok F hu a) fun u ⟨F', e, out⟩ =>
      ⟨F'.free, by rw [freed_gpr _ _ (by decide)]; exact e, by rw [freed_mem]; exact out⟩

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! ### `Ffdh.X86.Cached.Search.Exits`, which this module and modules that import it used -/

section

/-! # The key search's exits without an attempt (x86)

From a loop state, `exhausted` (a budget at zero) and `request` (the tape
too short) end the search with zeros at both outputs (`exhausted_ok`,
`request_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- A run's state, with the words a finished search leaves. -/
theorem St.done {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : KeySearchResult}
    (hs : ∀ d ∈ doneDs, d ∈ ds) (he : ∀ d ∈ doneDs, f d = doneF (ofState o) (o.gpr .esi) r d)
    (hout : Output (ofState o) r s.mem)
    (hsm : r.retries.keys ≤ 128 ∧ r.retries.scalars ≤ 128 ∧ r.used ≤ (ofState o).randLen) :
    Done (ofState o) o r s :=
  ⟨⟨h.abi, rfl⟩, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, (h.words.sub hs).congr he, hout, hsm⟩

theorem exhausted_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa exhausted s (Done p o ⟨.exhausted, used, []⟩) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  unfold exhausted terminal
  refine WP.seq (wp_movi fun t₁ U₁ => ?_)
  have S₁ := S.reg U₁ (Or.inl rfl)
  refine S₁.stw hA (d := keysOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ _ => ?_
  refine S₂.stw (hA.cons (by decide) (by decide)) (d := scalarsOff) (by decide) (by decide)
    fun t₃ S₃ G₃ _ _ _ => ?_
  refine S₃.stw ((hA.cons (by decide) (by decide)).cons (by decide) (by decide)) (d := requestOff)
    (by decide) (by decide) fun t₄ S₄ G₄ _ _ _ => ?_
  refine wp_movi fun t₅ U₅ => ?_
  have S₅ := S₄.reg U₅ (Or.inl rfl)
  refine S₅.stw (((hA.cons (by decide) (by decide)).cons (by decide) (by decide)).cons (by decide) (by decide))
    (d := statusOff) (by decide) (by decide) fun t₆ S₆ G₆ _ _ _ => WP.block_nil ?_
  have e₂ : t₂.gpr .eax = 0 := by rw [G₂, U₁.gpr]
  have e₃ : t₃.gpr .eax = 0 := by rw [G₃, e₂]
  simp only [U₁.gpr, e₂, e₃, U₅.gpr] at S₆
  have hA₆ : Aligned (statusOff :: requestOff :: scalarsOff :: keysOff :: liveDs) := by decide
  refine WP.mono (S₆.zeroOutputs hA₆ (by simp [upd, liveF, ofState, xOff, statusOff, requestOff, scalarsOff,
      keysOff]) (by simp [upd, liveF, ofState, yOff, statusOff, requestOff, scalarsOff, keysOff])
    (by simp [upd, liveF, ofState, lenOff, statusOff, requestOff, scalarsOff, keysOff]) (by decide) (by decide)
    (by decide)) fun u ⟨Su, Zx, Zy, _, _⟩ => ?_
  refine Su.done (by decide) ?_ ⟨Zx, Zy⟩ ⟨Nat.zero_le _, Nat.zero_le _, h.used_le⟩
  simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [upd, liveF, doneF, statusOff, requestOff, scalarsOff, keysOff, KeySearchResult.retries,
      KeySearchResult.status, ofState]

theorem request_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa request s (Done p o ⟨.entropy ⟨keys, scalars⟩, used, []⟩) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  unfold request
  refine WP.seq (S.ld (Or.inl rfl) (d := lenOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_)
  refine S₁.stw hA (d := requestOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ _ => ?_
  refine wp_movi fun t₃ U₃ => ?_
  have S₃ := S₂.reg U₃ (Or.inl rfl)
  refine S₃.stw (hA.cons (by decide) (by decide)) (d := statusOff) (by decide) (by decide)
    fun t₄ S₄ G₄ _ _ _ => WP.block_nil ?_
  simp only [g₁, U₃.gpr] at S₄
  have hA₄ : Aligned (statusOff :: requestOff :: liveDs) := by decide
  refine WP.mono (S₄.zeroOutputs hA₄ (by simp [upd, liveF, ofState, xOff, statusOff, requestOff])
    (by simp [upd, liveF, ofState, yOff, statusOff, requestOff])
    (by simp [upd, liveF, ofState, lenOff, statusOff, requestOff]) (by decide) (by decide)
    (by decide)) fun u ⟨Su, Zx, Zy, _, _⟩ => ?_
  refine Su.done (by decide) ?_ ⟨Zx, Zy⟩ ⟨h.keys_le, h.scalars_le, h.used_le⟩
  simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [upd, liveF, doneF, statusOff, requestOff, lenOff, KeySearchResult.retries, KeySearchResult.status,
      ofState]

end VG.Proof.Ffdh.X86.Cached.Search

end

end

/-! # After an attempt (x86)

`classify` consumes the attempt's `p_len` octets (`advance_ok`) and, by its
status, finishes the search with the key pair, or counts a rejection and
asks the loop for another attempt (`classify_ok`): the search from there
ends as the search from before the attempt does (`Same`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- Two searches that end alike: what a finished search leaves depends on its outcome and the octets
it consumed, not on the statuses before. -/
def Same (r₁ r₂ : KeySearchResult) : Prop := r₁.outcome = r₂.outcome ∧ r₁.used = r₂.used

theorem Same.refl (r : KeySearchResult) : Same r r := ⟨rfl, rfl⟩

theorem Same.trans {r₁ r₂ r₃ : KeySearchResult} (h₁ : Same r₁ r₂) (h₂ : Same r₂ r₃) : Same r₁ r₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem Done.congr {p : KPub} {o s : State} {r₁ r₂ : KeySearchResult} (h : Done p o r₁ s) (e : Same r₁ r₂) :
    Done p o r₂ s := by
  have es : r₁.status = r₂.status := by simp only [KeySearchResult.status, e.1]
  have er : r₁.retries = r₂.retries := by simp only [KeySearchResult.retries, e.1]
  refine ⟨h.input, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.congr fun d _ => ?_, ?_,
    by rw [← er, ← e.2]; exact h.small⟩
  · simp only [doneF, es, er, e.2]
  · have := h.output; unfold Output at this ⊢; rw [← e.1]; exact this

/-- A loop state after a rejection: the status word says so. -/
def Rej (p : KPub) (o : State) (used keys scalars : Nat) (s : State) : Prop :=
  Live p o used keys scalars s ∧ s.mem.readW (addr p.S statusOff) 32 = 4

/-- After an iteration from a loop state: the search from there finished, or a rejection counted
(status 2 or 3) and the loop state after it. -/
def Next (p : KPub) (o : State) (used keys scalars : Nat) (s : State) : Prop :=
  (Done p o (p.tail (randOf o) used keys scalars) s ∧
    ¬ (keys ≠ 0 ∧ scalars ≠ 0 ∧ used + p.len ≤ p.randLen ∧
      (attemptStatus .cached p.a p.len ((randOf o).drop used) = 2 ∨ attemptStatus .cached p.a p.len ((randOf o).drop used) = 3))) ∨
    (keys ≠ 0 ∧ scalars ≠ 0 ∧ used + p.len ≤ p.randLen ∧
      ((attemptStatus .cached p.a p.len ((randOf o).drop used) = 2 ∧ Rej p o (used + p.len) keys (scalars - 1) s) ∨
        (attemptStatus .cached p.a p.len ((randOf o).drop used) = 3 ∧ Rej p o (used + p.len) (keys - 1) 128 s)))

/-- A run's state with a loop state's words. -/
theorem St.live {o s : State} {used keys scalars : Nat}
    (h : St o liveDs (liveF (ofState o) (o.gpr .esi) used keys scalars) s) (hu : used ≤ (ofState o).randLen)
    (hk : keys ≤ 128) (hc : scalars ≤ 128) : Live (ofState o) o used keys scalars s :=
  ⟨⟨h.abi, rfl⟩, hu, hk, hc, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem advance_ok {o u : State} {e : BitVec 32} {used keys scalars : Nat}
    (S : St o liveDs (liveF (ofState o) e used keys scalars) u) (hr : used + (ofState o).len ≤ (ofState o).randLen)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o liveDs (liveF (ofState o) e (used + (ofState o).len) keys scalars) t → t.gpr .edx = u.gpr .eax →
      Frame [sR o] u.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (advance ++ rest)) u Q := by
  have hA := liveDs_aligned
  have hb := S.abi.rBound
  unfold advance
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun t₁ U₁ => ?_
  have S₁ := S.reg U₁ (Or.inr (Or.inr rfl))
  refine S₁.ld (Or.inr (Or.inl rfl)) (d := lenOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ m₂ => ?_
  refine S₂.ld (Or.inl rfl) (d := randOff) (by decide) (by decide) fun t₃ S₃ g₃ o₃ _ m₃ => ?_
  refine wp_add fun t₄ U₄ _ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA (d := randOff) (by decide) (by decide) fun t₅ S₅ G₅ _ _ F₅ => ?_
  have hA₅ := hA.cons (d := randOff) (by decide) (by decide)
  refine S₅.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ m₆ => ?_
  refine wp_sub fun t₇ U₇ _ => ?_
  have S₇ := S₆.reg U₇ (Or.inl rfl)
  refine S₇.stw hA₅ (d := leftOff) (by decide) (by decide) fun t₈ S₈ G₈ _ _ F₈ => ?_
  have hA₈ := hA₅.cons (d := leftOff) (by decide) (by decide)
  refine S₈.ld (Or.inl rfl) (d := usedOff) (by decide) (by decide) fun t₉ S₉ g₉ o₉ _ m₉ => ?_
  refine wp_add fun t₁₀ U₁₀ _ => ?_
  have S₁₀ := S₉.reg U₁₀ (Or.inl rfl)
  refine S₁₀.stw hA₈ (d := usedOff) (by decide) (by decide) fun t₁₁ S₁₁ G₁₁ _ _ F₁₁ => k t₁₁ ?_ ?_ ?_
  · -- The values stored.
    have c₃ : t₃.gpr .ecx = BitVec.ofNat 32 (ofState o).len := by rw [o₃ .ecx (by decide), g₂]; rfl
    have c₆ : t₆.gpr .ecx = BitVec.ofNat 32 (ofState o).len := by
      rw [o₆ .ecx (by decide), G₅, U₄.other .ecx (by decide), c₃]
    have c₉ : t₉.gpr .ecx = BitVec.ofNat 32 (ofState o).len := by
      rw [o₉ .ecx (by decide), G₈, U₇.other .ecx (by decide), c₆]
    have v₄ : t₄.gpr .eax = (ofState o).rp + BitVec.ofNat 32 (used + (ofState o).len) := by
      rw [U₄.gpr, g₃, c₃, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    have v₇ : t₇.gpr .eax = BitVec.ofNat 32 ((ofState o).randLen - (used + (ofState o).len)) := by
      rw [U₇.gpr, g₆, c₆, show upd (liveF (ofState o) e used keys scalars) randOff (t₄.gpr .eax) leftOff =
        BitVec.ofNat 32 ((ofState o).randLen - used) from rfl, sub_ofNat (by omega_arith), Nat.sub_add_eq]
    have v₁₀ : t₁₀.gpr .eax = BitVec.ofNat 32 (used + (ofState o).len) := by
      rw [U₁₀.gpr, g₉, c₉, show upd (upd (liveF (ofState o) e used keys scalars) randOff (t₄.gpr .eax)) leftOff
        (t₇.gpr .eax) usedOff = BitVec.ofNat 32 used from rfl, BitVec.ofNat_add_ofNat]
    rw [v₄, v₇, v₁₀] at S₁₁
    refine (S₁₁.sub fun d hd => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))).congr ?_
    simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) <;> simp [upd, liveF, randOff, leftOff, usedOff]
  · rw [G₁₁, U₁₀.other _ (by decide), o₉ _ (by decide), G₈, U₇.other _ (by decide), o₆ _ (by decide), G₅,
      U₄.other _ (by decide), o₃ _ (by decide), o₂ _ (by decide), U₁.gpr]

  · have e₄ : t₄.mem = u.mem := by rw [U₄.mem, m₃, m₂, U₁.mem]
    have e₇ : t₇.mem = t₅.mem := by rw [U₇.mem, m₆]
    have e₁₀ : t₁₀.mem = t₈.mem := by rw [U₁₀.mem, m₉]
    rw [e₄] at F₅; rw [e₇] at F₈; rw [e₁₀] at F₁₁
    exact (F₅.trans F₈).trans F₁₁

/-- `terminal k`: the budgets and the request zero, the status `k`. -/
theorem St.terminal {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (k : Nat) :
    WP isa (.block (VG.Impl.Ffdh.X86.KeySearch.terminal k)) s fun t =>
      St o (statusOff :: requestOff :: scalarsOff :: keysOff :: ds)
        (upd (upd (upd (upd f keysOff 0) scalarsOff 0) requestOff 0) statusOff (BitVec.ofNat 32 k)) t ∧
      Frame [sR o] s.mem t.mem := by
  unfold VG.Impl.Ffdh.X86.KeySearch.terminal
  refine wp_movi fun t₁ U₁ => ?_
  have S₁ := h.reg U₁ (Or.inl rfl)
  refine S₁.stw hA (d := keysOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ F₂ => ?_
  have hA₂ := hA.cons (d := keysOff) (by decide) (by decide)
  refine S₂.stw hA₂ (d := scalarsOff) (by decide) (by decide) fun t₃ S₃ G₃ _ _ F₃ => ?_
  have hA₃ := hA₂.cons (d := scalarsOff) (by decide) (by decide)
  refine S₃.stw hA₃ (d := requestOff) (by decide) (by decide) fun t₄ S₄ G₄ _ _ F₄ => ?_
  have hA₄ := hA₃.cons (d := requestOff) (by decide) (by decide)
  refine wp_movi fun t₅ U₅ => ?_
  have S₅ := S₄.reg U₅ (Or.inl rfl)
  refine S₅.stw hA₄ (d := statusOff) (by decide) (by decide) fun t₆ S₆ G₆ _ _ F₆ => WP.block_nil ?_
  have e₂ : t₂.gpr .eax = 0 := by rw [G₂, U₁.gpr]
  have e₃ : t₃.gpr .eax = 0 := by rw [G₃, e₂]
  rw [U₁.gpr, e₂, e₃, U₅.gpr] at S₆
  rw [U₅.mem] at F₆
  rw [U₁.mem] at F₂
  exact ⟨S₆, ((F₂.trans F₃).trans F₄).trans F₆⟩

/-- A scalar out of range: one fewer scalar, the status 4. -/
theorem St.rejectedScalar {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hd : scalarsOff ∈ ds) {c : Nat} (hc : f scalarsOff = BitVec.ofNat 32 c) (hc1 : 1 ≤ c) :
    WP isa (.block VG.Impl.Ffdh.X86.KeySearch.rejectedScalar) s fun t =>
      St o (statusOff :: scalarsOff :: ds) (upd (upd f scalarsOff (BitVec.ofNat 32 (c - 1))) statusOff 4) t := by
  unfold VG.Impl.Ffdh.X86.KeySearch.rejectedScalar
  refine h.ld (Or.inl rfl) (d := scalarsOff) hd (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine wp_subi fun t₂ U₂ _ _ => ?_
  have S₂ := S₁.reg U₂ (Or.inl rfl)
  refine S₂.stw hA (d := scalarsOff) (by decide) (by decide) fun t₃ S₃ G₃ _ _ _ => ?_
  have hA₃ := hA.cons (d := scalarsOff) (by decide) (by decide)
  refine wp_movi fun t₄ U₄ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA₃ (d := statusOff) (by decide) (by decide) fun t₅ S₅ _ _ _ _ => WP.block_nil ?_
  rw [U₂.gpr, g₁, hc, ofNat_pred hc1, U₄.gpr] at S₅
  exact S₅

/-- A degenerate public value: one fewer key, the scalar budget again, the status 4. -/
theorem St.rejectedPublic {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hd : keysOff ∈ ds) {k : Nat} (hk : f keysOff = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) :
    WP isa (.block VG.Impl.Ffdh.X86.KeySearch.rejectedPublic) s fun t =>
      St o (statusOff :: scalarsOff :: keysOff :: ds)
        (upd (upd (upd f keysOff (BitVec.ofNat 32 (k - 1))) scalarsOff 128) statusOff 4) t := by
  unfold VG.Impl.Ffdh.X86.KeySearch.rejectedPublic
  refine h.ld (Or.inl rfl) (d := keysOff) hd (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine wp_subi fun t₂ U₂ _ _ => ?_
  have S₂ := S₁.reg U₂ (Or.inl rfl)
  refine S₂.stw hA (d := keysOff) (by decide) (by decide) fun t₃ S₃ G₃ _ _ _ => ?_
  have hA₃ := hA.cons (d := keysOff) (by decide) (by decide)
  refine wp_movi fun t₄ U₄ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA₃ (d := scalarsOff) (by decide) (by decide) fun t₅ S₅ G₅ _ _ _ => ?_
  have hA₅ := hA₃.cons (d := scalarsOff) (by decide) (by decide)
  refine wp_movi fun t₆ U₆ => ?_
  have S₆ := S₅.reg U₆ (Or.inl rfl)
  refine S₆.stw hA₅ (d := statusOff) (by decide) (by decide) fun t₇ S₇ _ _ _ _ => WP.block_nil ?_
  rw [U₂.gpr, g₁, hk, ofNat_pred hk1, U₄.gpr, U₆.gpr] at S₇
  exact S₇

/-- The bytes at an output, through writes of the state. -/
theorem out_keep {o : State} (A : KeySearchABI o) {m m' : Mem} (h : Frame [sR o] m m') {i : Nat} (hi : i = 0 ∨ i = 2) :
    Spec.Rsa.bytesAt m' (argumentPointer o i) (arg o 7).toNat = Spec.Rsa.bytesAt m (argumentPointer o i) (arg o 7).toNat := by
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  refine bytes_frame h (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_singleton] at hr; subst hr
  rcases hi with rfl | rfl
  · rw [← xR_eq A]; exact A.xs
  · rw [← yR_eq A]; exact A.ys

theorem cmp_status {s t : State} {k j : Nat} (hk : k ≤ 3) (hj : j ≤ 3) (he : s.gpr .edx = BitVec.ofNat 32 k)
    (z : t.zf = some (s.gpr .edx - BitVec.ofNat 32 j == 0)) : isa.eval .e t = some (decide (k = j)) := by
  show t.zf = _
  rw [z, he, sub_beq (by omega_arith) (by omega_arith)]

theorem classify_ok {p : KPub} {o s₀ u : State} {used keys scalars : Nat} (h : Live p o used keys scalars s₀)
    (S : St o liveDs (liveF p (o.gpr .esi) used keys scalars) u)
    (he : u.gpr .eax = BitVec.ofNat 32 (attemptStatus .cached p.a p.len ((randOf o).drop used)))
    (ho : AttemptOut o used u.mem) (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : used + p.len ≤ p.randLen) :
    WP isa classify u (Next p o used keys scalars) := by
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hr' : (ofState o).len ≤ (randOf o).length - used := by
    simp only [randOf, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact Nat.le_sub_of_add_le' hr
  unfold classify
  refine WP.seq (advance_ok S hr fun t S' hed Ft => wp_cmpi fun t' F _ z => WP.block_nil ?_)
  have S'' := S'.fupd F
  have Ft' : Frame [sR o] u.mem t'.mem := by rw [F.mem]; exact Ft
  have hed' : t'.gpr .edx = BitVec.ofNat 32 (attemptStatus .cached (ofState o).a (ofState o).len ((randOf o).drop used)) := by
    rw [F.gpr, hed, he]
  have hedT : t.gpr .edx = BitVec.ofNat 32 (attemptStatus .cached (ofState o).a (ofState o).len ((randOf o).drop used)) :=
    hed.trans he
  have hst := attemptStatus_cases (policy := .cached) (ofState o).a (ofState o).len ((randOf o).drop used)
  have hle : attemptStatus .cached (ofState o).a (ofState o).len ((randOf o).drop used) ≤ 3 := by
    rcases hst with h1 | h1 | h1 <;> omega_arith
  rcases hst with h1 | h2 | h3
  · -- Accepted.
    refine WP.ite true (by rw [cmp_status hle (j := 1) (by decide) hedT z, h1]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (S''.terminal hA 1) fun v ⟨Sv, Fv⟩ => Or.inl ⟨?_, fun ⟨_, _, _, h⟩ => by
      rw [h1] at h; omega_arith⟩
    show Done _ _ (keyTail .cached _ _ _ _ _ _) v
    rw [keyTail_accepted hk hs hr' h1]
    refine Sv.done (by decide) ?_ ?_ ⟨Nat.zero_le _, Nat.zero_le _, by simp only [ofState] at hr ⊢; omega_arith⟩
    · simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        simp [upd, liveF, doneF, statusOff, requestOff, scalarsOff, keysOff, KeySearchResult.retries,
          KeySearchResult.status]
    · have h1' : keyStatus (ofState o).a (vettedScalarOfOctets (ofState o).a
          (List.take (arg o 7).toNat (List.drop used (randOf o)))) = 1 := h1
      have ho' := ho
      unfold AttemptOut at ho'
      dsimp only at ho'
      rw [ite_eq_left h1'] at ho'
      exact ⟨(out_keep A (Ft'.trans Fv) (Or.inl rfl)).trans ho'.1, (out_keep A (Ft'.trans Fv) (Or.inr rfl)).trans ho'.2⟩
  · -- A scalar out of range.
    refine WP.ite false (by rw [cmp_status hle (j := 1) (by decide) hedT z, h2]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ?_)
    have S₂ := S''.fupd F₂
    have hed₂ : t₂.gpr .edx = _ := (congrFun F₂.gpr .edx).trans hed'
    refine WP.ite true (by rw [cmp_status hle (j := 2) (by decide) hed' z₂, h2]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (S₂.rejectedScalar hA (by decide) (c := scalars) (by simp [liveF, scalarsOff]) (by omega_arith))
      fun v Sv => Or.inr ⟨hk, hs, hr, Or.inl ⟨h2, Sv.sub (fun d hd => by
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)) |>.congr ?_ |>.live (by omega_arith) hkl (by omega_arith),
        ?_⟩⟩
    · simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl) <;> simp [upd, liveF, statusOff, scalarsOff]
    · show v.mem.readW (addr (arg o 12) statusOff) 32 = 4
      rw [Sv.words.get (List.mem_cons_self ..)]; simp [upd, statusOff]
  · -- A degenerate public value.
    refine WP.ite false (by rw [cmp_status hle (j := 1) (by decide) hedT z, h3]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ?_)
    have S₂ := S''.fupd F₂
    have hed₂ : t₂.gpr .edx = _ := (congrFun F₂.gpr .edx).trans hed'
    refine WP.ite false (by rw [cmp_status hle (j := 2) (by decide) hed' z₂, h3]; rfl) (fun h => absurd h (by decide))
      (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₃ F₃ _ z₃ => WP.block_nil ?_)
    have S₃ := S₂.fupd F₃
    have hed₃ : t₃.gpr .edx = _ := (congrFun F₃.gpr .edx).trans hed₂
    refine WP.ite true (by rw [cmp_status hle (j := 3) (by decide) hed₂ z₃, h3]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (S₃.rejectedPublic hA (by decide) (k := keys) (by simp [liveF, keysOff]) (by omega_arith))
      fun v Sv => Or.inr ⟨hk, hs, hr, Or.inr ⟨h3, Sv.sub (fun d hd => by
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))) |>.congr ?_
        |>.live (by omega_arith) (by omega_arith) (by decide), ?_⟩⟩
    · simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl) <;> simp [upd, liveF, statusOff, scalarsOff, keysOff]
    · show v.mem.readW (addr (arg o 12) statusOff) 32 = 4
      rw [Sv.words.get (List.mem_cons_self ..)]; simp [upd, statusOff]

end VG.Proof.Ffdh.X86.Cached.Search
