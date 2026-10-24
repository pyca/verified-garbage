module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CallPre
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenVerified
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape

/-! # The attempt's call (x86)

`vg_ffdh_generate_key`, called with its arguments in the frame, returns the
status of the attempt on the tape's next `p_len` octets and writes its
outputs, changing memory only at the outputs, the working space and the
stack the controller uses (`call_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (argumentPointer)

theorem callee_stack : stackUse Impl.Ffdh.X86.GenerateKey.code = 172 := by rsa_stack_use

theorem callee_noSp : NoSp Impl.Ffdh.X86.GenerateKey.code := NoSp.of_all (by rsa_stack_shape)

/-- The bytes `[u, u + l)` of `n` at `p`. -/
theorem bytes_window (m : Mem) (p : Addr) {u l n : Nat} (h : u + l ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 u) l = ((Spec.Rsa.bytesAt m p n).drop u).take l := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega)
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What an attempt leaves at the outputs. -/
def AttemptOut (o : State) (used : Nat) (m : Mem) : Prop :=
  let a := (ofState o).a
  let x := scalarOfOctets a (((randOf o).drop used).take (arg o 7).toNat)
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
  have hw : ∀ r ∈ callWr o, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
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
    rcases hr with rfl | rfl
    · exact ⟨dR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨rR o, by simp, used, win_base A hu, hu⟩
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

/-- The state, through the call's writes. -/
theorem stR_eq {o : State} : stR (arg o 12) = sR o := rfl

/-- The call's return address. -/
theorem ret_eq {o t : State} (A : KeySearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 172 := by
  rw [esp_sub4 A he, sw_sub A (by decide)]

/-- The stack below the call. -/
theorem below_eq {o t : State} (A : KeySearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    below (t.gpr .esp) (stackUse Impl.Ffdh.X86.GenerateKey.code + 4) = ⟨low o, 176⟩ := by
  have h1 : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  have hl := low_toNat A
  have := (o.gpr .esp).isLt
  have e : (o.gpr .esp - BitVec.ofNat 32 argsBytes - BitVec.ofNat 32 (172 + 4)).setWidth 64 = low o := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, hl, argsBytes]
    omega
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
  have fe : ∀ v : BitVec 32, Frame [⟨low o + BitVec.ofNat 64 172, 4⟩] t.mem
      (t.mem.writeW (low o + BitVec.ofNat 64 172) v) := fun v =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  have dE : ∀ v : BitVec 32, Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v) (argumentPointer o 5)
      (arg o 6).toNat = (ofState o).dom := fun v => by
    rw [bytes_frame (fe v) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.lowD.sub_left Rs).symm) (by omega),
      bytes_frame h.frame (dom_apart A) (by omega)]; rfl
  have rE : ∀ v : BitVec 32, Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v)
      ((arg o 8 + BitVec.ofNat 32 used).setWidth 64) (arg o 7).toNat =
      ((randOf o).drop used).take (arg o 7).toNat := fun v => by
    have W := win_sub A hu
    rw [bytes_frame (fe v) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ((A.lowRand.sub_left Rs).sub_right W).symm)
      (by omega), bytes_frame h.frame (fun r hr => (rand_apart A r hr).sub_left W) (by omega),
      win_base A hu, bytes_window _ _ hu]
  exact ⟨dE v, rE v⟩

theorem call_ok {o t : State} {e : BitVec 32} {used keys scalars : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used keys scalars) t)
    (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) (ha : ArgsAt o used 11 t.mem) :
    WP isa (.call Spec.Ffdh.generateKeyApi.name Impl.Ffdh.X86.GenerateKey.code) t fun u =>
      Fr o liveDs (liveF (ofState o) e used keys scalars) u ∧
      u.gpr .eax = BitVec.ofNat 32 (attemptStatus (ofState o).a (arg o 7).toNat ((randOf o).drop used)) ∧
      AttemptOut o used u.mem := by
  have A := h.abi
  have h1 : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 44 := by
    rw [h.esp]; exact VG.X86.sub_toNat (by unfold argsBytes; omega)
  obtain ⟨hc, hcw⟩ := call_covers (t := t) A hu h.rd h.wr
  refine WP.call Proof.Ffdh.X86.KeyGen.verified.1 callee_noSp (by rw [callee_stack, hn]; omega)
    (call_pre A hu h.esp ha) hc hcw fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  have hp := hpost
  sig_post [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes] at hp
  simp only [ce_arg A h.esp ha _ _ (show 0 < 11 by decide),
    ce_arg A h.esp ha _ _ (show 2 < 11 by decide), ce_arg A h.esp ha _ _ (show 4 < 11 by decide), ce_arg A h.esp ha _ _ (show 5 < 11 by decide),
    ce_arg A h.esp ha _ _ (show 6 < 11 by decide), ce_arg A h.esp ha _ _ (show 7 < 11 by decide),
    ce_arg A h.esp ha _ _ (show 8 < 11 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, ret_eq A h.esp] at hp
  have hpl := A.pLen
  unfold Spec.Ffdh.pLenValid at hpl
  have dE := fun v => (entry_bytes h hu v).1
  have rE := fun v => (entry_bytes h hu v).2
  simp only [dE, rE] at hp
  obtain ⟨hr, hout⟩ := hp A.domValid
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  have hS := A.sBound
  have hA : Aligned liveDs := by decide
  have Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  have xr := xR_eq A
  have yr := yR_eq A
  have fr : Frame (frameR o) t.mem u.mem := hf.sub fun r hr => by
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
    NoSp (Code.seq (.block arguments) (.call Spec.Ffdh.generateKeyApi.name Impl.Ffdh.X86.GenerateKey.code) :
      Prog isa) := NoSp.of_all (by rsa_stack_shape)

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
      u.gpr .eax = BitVec.ofNat 32 (attemptStatus p.a p.len ((randOf o).drop used)) ∧ AttemptOut o used u.mem := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have h1 : 220 ≤ (o.gpr .esp).toNat := A.stackLow
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [S.esp]; unfold argsBytes; omega) body_noSp ?_
  refine WP.seq (WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ?_)
  exact WP.mono (call_ok F hu a) fun u ⟨F', e, out⟩ =>
    ⟨F'.free, by rw [freed_gpr _ _ (by decide)]; exact e, by rw [freed_mem]; exact out⟩

end VG.Proof.Ffdh.X86.KeySearch
