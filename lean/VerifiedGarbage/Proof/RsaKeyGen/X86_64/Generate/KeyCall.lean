module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.KeyArgs
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key's call

Its regions: the key's buffer's slots, the exponent in the state, the
working space, its stack arguments and its return address; its
precondition at its entry, from the controller's.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The key's buffer's slot `j`, of `n` octets. -/
abbrev kSlot (p : GenPublic) (j n : Nat) : Region := ⟨p.slot j, n⟩

/-- `n`, of `2 p_len` octets at the key's buffer. -/
abbrev kN (p : GenPublic) : Region := ⟨p.kp, 2 * p.L⟩

/-- The key's stack arguments, and its return address. -/
abbrev kA (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 256, 96⟩
abbrev kRet (p : GenPublic) : Region := ⟨p.sp - BitVec.ofNat 64 264, 8⟩

/-- The regions the key reads, and those it writes. -/
def kReads (p : GenPublic) : List Region := [rE p, kA p]
def kWrites (p : GenPublic) : List Region :=
  [kN p, kSlot p 2 (2 * p.L), kSlot p 4 p.L, kSlot p 5 p.L, kSlot p 6 p.L, kSlot p 7 p.L, kSlot p 8 p.L, rS p]

/-- The key's entry, as the call makes it. -/
abbrev callK (p : GenPublic) (u : State) : State := u.callEntry.withRegions (kReads p) (kWrites p)

section

variable {p : GenPublic}

theorem kA_sub : Region.Sub (kA p) (cStack p) := Offset.sub_below _ (by decide) (by decide)

theorem kRet_sub : Region.Sub (kRet p) (cStack p) := Offset.sub_below _ (by decide) (by decide)

theorem ret_kA : (kRet p).Disjoint (kA p) :=
  disj_of_sep (Offset.sep_below p.sp 552 (a := 264) (n := 8) (b := 256) (k := 96) (by decide) (by decide)
    (Or.inl (by decide)) (by decide) (by decide))

theorem kk (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) : (kSlot p i a).Disjoint (kSlot p j b) :=
  slot_disjoint p.kp h (by have := hf.nK; omega) (by have := hf.nK; omega)

theorem kN_slot (hf : CFacts p) {j b : Nat} (h : 2 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (kN p).Disjoint (kSlot p j b) := by
  have := slot_disjoint p.kp (d := 0) (n := 2 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

theorem kSlot_sub {j n : Nat} (h : j * p.L + n ≤ 9 * p.L) : Region.Sub (kSlot p j n) (cK p) := slot_sub _ h

theorem kN_sub : Region.Sub (kN p) (cK p) := Region.sub_prefix (by omega)

end

theorem F_96 (p : GenPublic) : p.F - BitVec.ofNat 64 96 = p.sp - BitVec.ofNat 64 256 := by
  rw [GenPublic.F, BitVec.sub_sub]; rfl

section

variable {p : GenPublic} {s u : State}

theorem callK_rsp (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256) :
    (callK p u).gpr .rsp = p.sp - BitVec.ofNat 64 264 := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, hu, BitVec.sub_sub]
  rfl

theorem callK_gpr {r : Reg} (hr : r ≠ .rsp) : (callK p u).gpr r = u.gpr r := by
  simp only [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem callK_argAddr (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256) (j : Nat) :
    stackArgAddr (callK p u) j = p.sp - BitVec.ofNat 64 256 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
  rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]

theorem callK_arg (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) (j : Nat) (hj : j < 12) :
    stackArg (callK p u) j = frameValue (keyValues p) j (word s.mem (p.sp - BitVec.ofNat 64 256) (8 * j)) := by
  have e1 : p.sp - BitVec.ofNat 64 256 - 8 + BitVec.ofNat 64 (8 + 8 * j) =
      p.sp - BitVec.ofNat 64 256 + BitVec.ofNat 64 (8 * j) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      BitVec.sub_add_cancel]
  have sep : Mem.Sep (p.sp - BitVec.ofNat 64 256 + BitVec.ofNat 64 (8 * j)) (64 / 8)
      (p.sp - BitVec.ofNat 64 256 - 8) (64 / 8) := by
    have := Offset.sep (p.sp - BitVec.ofNat 64 256 - 8) (d := 8 + 8 * j) (n := 8) (e := 0) (k := 8)
      (.inr (by omega)) (by omega) (by decide)
    rw [e1, BitVec.add_zero] at this
    exact this
  unfold stackArg
  rw [callK_argAddr hu, State.withRegions_mem, State.callEntry_mem, hu, Mem.readW_writeW_sep sep (by decide),
    hm, F_96]
  exact writeFrame_word _ _ _ (keyValues_bound20 p) j (by omega)

/-- The key's stack arguments. -/
theorem callK_args (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) :
    Key.arg (callK p u) 0 = p.slot 5 ∧ Key.arg (callK p u) 1 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 2 = p.slot 6 ∧ Key.arg (callK p u) 3 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 4 = p.slot 7 ∧ Key.arg (callK p u) 5 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 6 = p.slot 8 ∧ Key.arg (callK p u) 7 = BitVec.ofNat 64 p.L ∧
      Key.arg (callK p u) 8 = p.stp + BitVec.ofNat 64 48 ∧ Key.arg (callK p u) 9 = BitVec.ofNat 64 8 ∧
      Key.arg (callK p u) 10 = p.B ∧ Key.arg (callK p u) 11 = BitVec.ofNat 64 (p.Z / 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [Key.arg, callK_arg hu hm _ (by decide)]; rfl)

/-- The call's entry writes only the controller's stack below its frame. -/
theorem callK_frame (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) :
    Frame [cStack p] s.mem (callK p u).mem := by
  have h1 : Frame [cStack p] s.mem u.mem := by
    rw [hm, F_96]
    apply (Search.writeFrame_frame_size _ _ (keyValues p) (size := 96) (by decide) (keyValues_bound p)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, kA_sub⟩
  refine h1.trans ?_
  simp only [State.withRegions_mem, State.callEntry_mem]
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
  rw [hu, BitVec.sub_sub]
  rw [show p.sp - (BitVec.ofNat 64 256 + 8) = p.sp - BitVec.ofNat 64 552 + BitVec.ofNat 64 288 by
    rw [show BitVec.ofNat 64 256 + 8 = BitVec.ofNat 64 264 from rfl]
    exact Offset.sub_ofNat_eq _ (by decide)]
  exact Offset.contains_base _ (by decide) (by decide)

end

/-! ## The key's precondition -/

/-- The key's precondition at its entry. -/
theorem callK_pre {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s)
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256) (ha : KeyRegs p u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) :
    Key.keyPre (callK p u) := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := callK_args (s := s) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hsp := callK_rsp (p := p) hu
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have t8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by rw [toNat_ofNat_lt hf.z64]; exact hf.z8
  have hargs : stackArgAddr (callK p u) 0 = p.sp - BitVec.ofNat 64 256 := by
    rw [callK_argAddr hu, Nat.mul_zero, BitVec.add_zero]
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, sS, sT, -⟩ := hst
  have hn := hf.nK
  -- The key's buffer's regions.
  have s2 : Region.Sub (kSlot p 2 (2 * p.L)) (cK p) := kSlot_sub (by omega)
  have s4 : Region.Sub (kSlot p 4 p.L) (cK p) := kSlot_sub (by omega)
  have s5 : Region.Sub (kSlot p 5 p.L) (cK p) := kSlot_sub (by omega)
  have s6 : Region.Sub (kSlot p 6 p.L) (cK p) := kSlot_sub (by omega)
  have s7 : Region.Sub (kSlot p 7 p.L) (cK p) := kSlot_sub (by omega)
  have s8 : Region.Sub (kSlot p 8 p.L) (cK p) := kSlot_sub (by omega)
  have sN : Region.Sub (kN p) (cK p) := kN_sub
  have kE {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (rE p) := (hf.kT.sub_left hR).sub_right rE_sub
  have kS {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (rS p) := hf.kS.sub_left hR
  have kAr {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (kA p) := (sK.sub_left hR).sub_right kA_sub
  have kR {R : Region} (hR : Region.Sub R (cK p)) : (kRet p).Disjoint R :=
    ((sK.sub_left hR).sub_right kRet_sub).symm
  simp only [Key.keyPre, Key.args, Key.ret, callK_gpr (show Reg.rdi ≠ .rsp by decide),
    callK_gpr (show Reg.rsi ≠ .rsp by decide), callK_gpr (show Reg.rdx ≠ .rsp by decide),
    callK_gpr (show Reg.rcx ≠ .rsp by decide), callK_gpr (show Reg.r8 ≠ .rsp by decide),
    callK_gpr (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11, tl, t2, t8, tz, hargs, hsp, State.withRegions_rd, State.withRegions_wr]
  refine ⟨?_, rfl, rfl, kN_slot hf (by decide) (by omega), kN_slot hf (by decide) (by omega),
    kN_slot hf (by decide) (by omega), kN_slot hf (by decide) (by omega), kN_slot hf (by decide) (by omega),
    kN_slot hf (by decide) (by omega), kE sN, kS sN, kAr sN,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kE s2, kS s2, kAr s2,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega), kE s4, kS s4, kAr s4,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega),
    kk hf (by omega) (by omega) (by omega), kE s5, kS s5, kAr s5,
    kk hf (by omega) (by omega) (by omega), kk hf (by omega) (by omega) (by omega), kE s6, kS s6, kAr s6,
    kk hf (by omega) (by omega) (by omega), kE s7, kS s7, kAr s7,
    kE s8, kS s8, kAr s8,
    (hf.sT.sub_right rE_sub).symm, sS.sub_right kA_sub,
    kR sN, kR s2, kR s4, kR s5, kR s6, kR s7, kR s8,
    ((sT.sub_left rE_sub).sub_right kRet_sub).symm, (sS.sub_right kRet_sub).symm, ret_kA,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hL1, hL2, hL3⟩, trivial, trivial, trivial, trivial, trivial, trivial, by decide, by decide, ?_⟩
  · have := hf.room
    have := hf.top
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 264).toNat = 264 from rfl]; omega),
      show (BitVec.ofNat 64 264).toNat = 264 from rfl]
    omega
  · omega
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · exact slot_nowrap hf (by omega)
  · rw [BitVec.toNat_add, toNat_ofNat_lt (by decide)]; have := hf.nT; omega
  · exact hf.nS
  · have := hf.scratch
    rw [toNat_ofNat_lt hf.z64]
    exact this

end VG.Proof.RsaKeyGen.X86_64.Generate
