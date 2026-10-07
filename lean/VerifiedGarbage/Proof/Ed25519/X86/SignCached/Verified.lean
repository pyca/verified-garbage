import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Ed25519.X86.SignCached
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CT

/-! Merged from `Proof.Ed25519.X86.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym combConsts)

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else
    if a = 0x900d then 0x30 else if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else 0

theorem sat_seed : Spec.Ed25519.bytesAt satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩]
  syms _ := 0x100000

theorem sat_arg (j : Nat) (hj : j < 6) : arg satState j = Mem.readW satMem (argAddr satState j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith satMem _ = _
  rw [satMemWith_out]
  have : ∀ j < 6, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr satState j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega)

theorem sat_bytes (a : Addr) (ha : ∀ i < 32, 8 * 32 * 96 ≤ (a + BitVec.ofNat 64 i - 0x100000).toNat) :
    Spec.Ed25519.bytesAt (satMemWith satMem) a 32 = Spec.Ed25519.bytesAt satMem a 32 := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun i hi => satMemWith_out _ (ha i (List.mem_range.mp hi))

theorem sat_pair : Spec.Ed25519.bytesAt (satMemWith satMem) 0x3000 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt (satMemWith satMem) 0x2000 32) := by
  rw [sat_bytes _ (by decide), sat_bytes _ (by decide), sat_seed, sat_key]
  rfl

theorem sat : (Spec.Ed25519.signCachedContract (X86.abi.withConsts combConsts) 280).pre satState := by
  have hl := combWords_length
  have a0 : arg satState 0 = 0x1000 := (sat_arg 0 (by decide)).trans (by decide)
  have a1 : arg satState 1 = 0x2000 := (sat_arg 1 (by decide)).trans (by decide)
  have a2 : arg satState 2 = 0x3000 := (sat_arg 2 (by decide)).trans (by decide)
  have a3 : arg satState 3 = 0x4000 := (sat_arg 3 (by decide)).trans (by decide)
  have a4 : arg satState 4 = 0 := (sat_arg 4 (by decide)).trans (by decide)
  have a5 : arg satState 5 = 0x5000 := (sat_arg 5 (by decide)).trans (by decide)
  have held : TblWords ((satState.syms combSym).setWidth 64) satState.mem := satMemWith_held satMem
  have pair := sat_pair
  generalize e : satState = s
  sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3, a4, a5]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | exact pair | decide

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
open VG.Impl.Ed25519.X86 (combSym combConsts)

def signWide : Contract isa := { signCachedLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, msg, TBL ((s.syms combSym).setWidth 64)] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) ∧
      CombHeld s [out, scr, stk, ret] }

theorem signWide_pre (s : State) (h : signWide.pre s) :
    signCachedLocal.pre (s.withRegions (signRd s) (signWr s)) := by
  simp only [signCachedLocal, signRd, signWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_syms, CombHeld]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem signWide_implies :
    signWide.Implies (Spec.Ed25519.signCachedContract (X86.abi.withConsts combConsts) 280) where
  pre s h := by
    sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h280, hsp, hd, held, hfit, hdw, tret, tstk, ht, hw, os, op, om, oc, oa, sc, -, pc, -,
      mc, -, ca, ro, rs, rp, rm, rc, -, ko, ks, kp, km, kc, -, f0, f1, f2, f3, f5, hk⟩ := h
    refine ⟨?_, hw, os, op, om, oa, oc, ko, ro, sc, pc, mc, ca.symm, rs, rp, rm, rc, ks, kp, km, kc,
      f0, f1, f2, f3, f5, h280, by omega, hk, held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact tstk
      · exact tret
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, h4, h5, hsy⟩
  sat := ⟨satState, sat⟩

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.SignCached
materialize_code code
end VG.Impl.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (combConsts)

theorem signCached_verified :
    Verified X86.target code (Spec.Ed25519.signCachedContract (X86.abi.withConsts combConsts) 280) := by
  have hsat := signWide_implies.sat_left
  have satLocal : ∃ s, signCachedLocal.pre s := hsat.elim fun s h => ⟨_, signWide_pre s h⟩
  have verifiedLocal : Verified X86.target code signCachedLocal :=
    Verified.of_correct (fun _ h => signCached_ok h) signCached_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal signRd signWr signWide_pre
    ?_ ?_ ?_ ?_ hsat) signWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signRd, signWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_syms] using h

end VG.Proof.Ed25519.X86.SignCached
