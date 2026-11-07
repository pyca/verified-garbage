module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Classify
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Contract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Key
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Correct
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! # RSA key generation's controller on PPC64LE: the key's call and the loop -/

@[expose] public section

/-! ## The controller's call of the key (PPC64LE)

`n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` at the key's buffer's slots 0, 2,
4, 5, 6, 7 and 8; the exponent the state's last word; the working space. The
ten stack arguments at offset 96 of the call's frame of 176 bytes, at
`sp - 272` for the controller's stack pointer on entry. The key's regions are
its outputs, the exponent, the working space and its stack arguments; it uses
no stack below its caller's.
-/

namespace VG.Proof.RsaKeyGen.PPC64LE.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.RsaKeyGen.PPC64LE.Search (WP.keepS)

/-! ## The key's arguments -/

/-- The key's stack arguments. -/
def keyValues (p : GenPublic) : List (Nat × BitVec 64) :=
  [(0, p.slot 6), (1, BitVec.ofNat 64 p.L), (2, p.slot 7), (3, BitVec.ofNat 64 p.L), (4, p.slot 8),
    (5, BitVec.ofNat 64 p.L), (6, p.stp + BitVec.ofNat 64 48), (7, BitVec.ofNat 64 8), (8, p.B),
    (9, BitVec.ofNat 64 (p.Z / 8))]

theorem keyValues_bound (p : GenPublic) : ∀ e ∈ keyValues p, 8 * e.1 + 8 ≤ 80 := by
  simp only [keyValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem keyValues_bound20 (p : GenPublic) : ∀ e ∈ keyValues p, e.1 < 20 := fun e he => by
  have := keyValues_bound p e he; omega

/-- The key's arguments in registers. -/
def KeyRegs (p : GenPublic) (s : State) : Prop :=
  s.gpr .r3 = p.kp ∧ s.gpr .r4 = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .r5 = p.slot 2 ∧
    s.gpr .r6 = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .r7 = p.slot 4 ∧ s.gpr .r8 = BitVec.ofNat 64 p.L ∧
    s.gpr .r9 = p.slot 5 ∧ s.gpr .r10 = BitVec.ofNat 64 p.L

/-- The key call's stack pointer. -/
abbrev keySp (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 368

theorem keySp_eq (p : GenPublic) : p.F - 80 - BitVec.ofNat 64 176 = keySp p := by
  rw [GenPublic.F, BitVec.sub_sub, BitVec.sub_sub]; rfl

/-- The key call's frame, its stack arguments stored. -/
abbrev keyMem (p : GenPublic) (s : State) : Mem :=
  writeFrame (allocated 176 s).mem (keySp p + BitVec.ofNat 64 96) (keyValues p)

/-- The key's stack arguments' region. -/
abbrev kA (p : GenPublic) : Region := ⟨keySp p + BitVec.ofNat 64 96, 80⟩

theorem kA_eq (p : GenPublic) : keySp p + BitVec.ofNat 64 96 = p.sp - BitVec.ofNat 64 272 :=
  (Offset.sub_ofNat_eq p.sp (by decide : 272 ≤ 368)).symm

theorem kA_stk (p : GenPublic) : Region.Sub (kA p) (rStk p) := by
  rw [kA, kA_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem rStk_sub (p : GenPublic) : Region.Sub (rStk p) (cStack p) := Region.sub_prefix (by decide)

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem alloc_key_sp (h : GenFrame p original used st s) : (allocated 176 s).sp = keySp p := by
  show s.sp - _ = _
  rw [h.sp, keySp_eq]

theorem alloc_key_wr (h : GenFrame p original used st s) :
    (allocated 176 s).wr = ⟨keySp p + 32, 144⟩ :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 176 + 32, 176 - 32⟩ : Region) :: s.wr = _
  rw [h.sp, keySp_eq]

/-- The key call's frame writes only the stack below the frame saving the
link register. -/
theorem key_low_frame (h : GenFrame p original used st s) : Frame [rStk p] s.mem (keyMem p s) := by
  have hb : Frame [rStk p] s.mem (allocated 176 s).mem := by
    refine Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
    rw [h.sp, keySp_eq]
    simp only [rStk, keySp]
    exact Offset.contains_below p.sp (a := 368) (b := stackUse) (by decide) (by decide) (by decide)
  refine hb.trans ((writeFrame_frame_size _ _ (keyValues p) (size := 80) (by decide)
    (keyValues_bound p)).sub fun r hr => ?_)
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, kA_stk p⟩

theorem rStk_callChanges (h : GenFrame p original used st s) :
    ∃ q ∈ GenInput.callChanges original, Region.Sub (rStk p) q := by
  have hS : (⟨original.sp - BitVec.ofNat 64 stackUse, 944⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 stackUse, 944⟩ := by rw [← h.input.2]; rfl
  refine ⟨⟨original.sp - BitVec.ofNat 64 stackUse, 944⟩, by simp [GenInput.callChanges], ?_⟩
  rw [hS]; exact Region.sub_prefix (by decide)

theorem key_args_frame (h : GenFrame p original used st s) :
    Frame (GenInput.callChanges original) s.mem (keyMem p s) := by
  obtain ⟨q, hq, hs⟩ := rStk_callChanges h
  exact (key_low_frame h).sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨q, hq, hs⟩

/-- The registers the key's stack arguments' block writes. -/
abbrev keyStackRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem slot_succ (p : GenPublic) (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
  rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; rw [Nat.succ_mul]

theorem key_stack_ok (h : GenFrame p original used st s) :
    WP isa (.block keyStack) (allocated 176 s) fun u =>
      (u.mem = keyMem p s ∧ Keep keyStackRegs (allocated 176 s) u) ∧ u.syms = (allocated 176 s).syms := by
  have hl := h.frame_ldA (t := allocated 176 s) (k := 176) rfl
  have hsp := alloc_key_sp h
  have haw := alloc_key_wr h
  have hw : ∀ d, 32 ≤ d → d + 8 ≤ 176 → InRegions (allocated 176 s).wr (keySp p + BitVec.ofNat 64 d) 8 :=
    fun d h1 hd => ⟨⟨keySp p + 32, 144⟩, by rw [haw]; exact List.mem_cons_self .., by
      rw [show keySp p + BitVec.ofNat 64 d = keySp p + 32 + BitVec.ofNat 64 (d - 32) by
        rw [BitVec.add_assoc]
        congr 1
        rw [show d = 32 + (d - 32) by omega, BitVec.ofNat_add, Nat.add_sub_cancel_left]; rfl]
      exact Offset.contains_base _ (by omega) (by omega)⟩
  have hf := alloc_frame h (k := 176) (by decide) (by decide)
  have hv0 := h.call_word hf (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have hv1 := h.call_word hf (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv5 := h.call_word hf (j := 5) (v := p.B) (by simp [GenPublic.headers])
  have hv6 := h.call_word hf (j := 6) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := h.call_word hf (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1 hv5 hv6 hv7
  have hl0 : InRegions ((allocated 176 s).rd ++ (allocated 176 s).wr) p.F 8 := by
    simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h31 : (allocated 176 s).gpr .r31 = p.F := h.r31
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have h6 : p.kp + (BitVec.ofNat 64 p.L <<< 2 + BitVec.ofNat 64 p.L <<< 1) = p.slot 6 := by
    rw [SearchInit.shl_ofNat _ _ (by omega), SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat,
      GenPublic.slot]
    congr 2; omega
  have h67 := slot_succ p 6
  have h78 := slot_succ p 7
  have ea : ∀ t : State, exec (.addSp .r11 96) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 96)) := by
    intro t; simp [exec]
  refine WP.keepS keyStackRegs ?_ (by decide)
  unfold keyStack keyMem writeFrame keyValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, ea, hsp, h31, hl0, hl 8 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hv0, hv1, hv5, hv6, hv7, h6, h67, h78, exec_li (show 8 < 2 ^ 15 by decide),
    hw 96 (by decide) (by decide), hw 104 (by decide) (by decide), hw 112 (by decide) (by decide),
    hw 120 (by decide) (by decide), hw 128 (by decide) (by decide), hw 136 (by decide) (by decide),
    hw 144 (by decide) (by decide), hw 152 (by decide) (by decide), hw 160 (by decide) (by decide),
    hw 168 (by decide) (by decide), off, BitVec.add_zero]

/-- The registers the key's register arguments' block writes. -/
abbrev keyArgRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

theorem key_args_ok {u : State} (h : GenFrame p original used st s) (hm : u.mem = keyMem p s)
    (ku : Keep keyStackRegs (allocated 176 s) u) :
    WP isa (.block keyArgs) u fun v =>
      ((KeyRegs p v ∧ v.mem = u.mem) ∧ Keep keyArgRegs u v) ∧ v.syms = u.syms := by
  have hl := h.frame_ldA (t := u) (k := 176) ku.wr
  have hf := key_args_frame h
  rw [← hm] at hf
  have hv0 := h.call_word hf (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have hv1 := h.call_word hf (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1
  have hl0 : InRegions (u.rd ++ u.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h31 : u.gpr .r31 = p.F := (ku.gpr .r31 (by decide)).trans h.r31
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have h2 : BitVec.ofNat 64 p.L <<< 1 = BitVec.ofNat 64 (2 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h24 : p.slot 2 + BitVec.ofNat 64 (2 * p.L) = p.slot 4 := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  have h45 := slot_succ p 4
  have hs2 : p.kp + BitVec.ofNat 64 (2 * p.L) = p.slot 2 := rfl
  refine WP.keepS keyArgRegs ?_ (by decide)
  unfold keyArgs KeyRegs
  prun [ldf, h31, hl0, hl 8 (by decide), hv0, hv1, h2, hs2, h24, h45, BitVec.add_zero] <;>
  first | rfl | exact ⟨rfl, rfl⟩

end

/-! ## The key's call -/

/-- The key's buffer's slot `j`, of `n` octets. -/
abbrev kSlot (p : GenPublic) (j n : Nat) : Region := ⟨p.slot j, n⟩

/-- `n`, of `2 p_len` octets at the key's buffer. -/
abbrev kN (p : GenPublic) : Region := ⟨p.kp, 2 * p.L⟩

/-- The regions the key reads, and those it writes. -/
def kReads (p : GenPublic) : List Region := [rE p, kA p]
def kWrites (p : GenPublic) : List Region :=
  [kN p, kSlot p 2 (2 * p.L), kSlot p 4 p.L, kSlot p 5 p.L, kSlot p 6 p.L, kSlot p 7 p.L, kSlot p 8 p.L, rS p]

/-- The key's entry, as the call makes it. -/
abbrev callK (p : GenPublic) (u : State) : State := u.callEntry.withRegions (kReads p) (kWrites p)

section

variable {p : GenPublic}

theorem kk (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) : (kSlot p i a).Disjoint (kSlot p j b) :=
  slot_disjoint p.kp h (by have := hf.nK; omega) (by have := hf.nK; omega)

theorem kN_slot (hf : CFacts p) {j b : Nat} (h : 2 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (kN p).Disjoint (kSlot p j b) := by
  have := slot_disjoint p.kp (d := 0) (n := 2 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

theorem kSlot_sub {j n : Nat} (h : j * p.L + n ≤ 9 * p.L) : Region.Sub (kSlot p j n) (cK p) := slot_sub _ h

theorem kN_sub (hf : CFacts p) : Region.Sub (kN p) (cK p) := Region.sub_prefix (by have := hf.len.1; omega)

end

section

variable {p : GenPublic} {s u : State}

theorem callK_gpr {r : Reg} (hr : r ∉ linkRegs) : (callK p u).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem callK_sp : (callK p u).sp = u.sp := rfl

theorem callK_mem : (callK p u).mem = u.mem := rfl

/-- The key's stack arguments. -/
theorem callK_args (hu : u.sp = keySp p) (hm : u.mem = keyMem p s) :
    stackArg (callK p u) 0 = p.slot 6 ∧ stackArg (callK p u) 1 = BitVec.ofNat 64 p.L ∧
      stackArg (callK p u) 2 = p.slot 7 ∧ stackArg (callK p u) 3 = BitVec.ofNat 64 p.L ∧
      stackArg (callK p u) 4 = p.slot 8 ∧ stackArg (callK p u) 5 = BitVec.ofNat 64 p.L ∧
      stackArg (callK p u) 6 = p.stp + BitVec.ofNat 64 48 ∧ stackArg (callK p u) 7 = BitVec.ofNat 64 8 ∧
      stackArg (callK p u) 8 = p.B ∧ stackArg (callK p u) 9 = BitVec.ofNat 64 (p.Z / 8) := by
  have hw (j : Nat) (hj : j < 10) : stackArg (callK p u) j =
      frameValue (keyValues p) j (word (allocated 176 s).mem (keySp p + BitVec.ofNat 64 96) (8 * j)) := by
    unfold stackArg stackArgAddr
    rw [callK_sp, callK_mem, hu, hm, ← writeFrame_word _ _ _ (keyValues_bound20 p) j (by omega)]
    simp only [word, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 3
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [hw _ (by decide)]; rfl)

theorem callK_argAddr (hu : u.sp = keySp p) : stackArgAddr (callK p u) 0 = keySp p + BitVec.ofNat 64 96 := by
  simp only [stackArgAddr, callK_sp, hu]

end

/-! ## The key's precondition -/

/-- The key's precondition at its entry. -/
theorem callK_pre {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hu : u.sp = keySp p) (ha : KeyRegs p u)
    (hm : u.mem = keyMem p s) :
    Key.keyP.pre (callK p u) := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := callK_args (s := s) hu hm
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have t8 : (BitVec.ofNat 64 8).toNat = 8 := rfl
  have tz : (BitVec.ofNat 64 (p.Z / 8)).toNat * 8 = p.Z := by rw [toNat_ofNat_lt hf.z64]; exact hf.z8
  have hargs := callK_argAddr (p := p) hu
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, sS, sT, -⟩ := hst
  have hn := hf.nK
  have hroom := hf.room
  have hsu : stackUse = 1088 := rfl
  have kAs : Region.Sub (kA p) (cStack p) := fun x hx => rStk_sub p x (kA_stk p x hx)
  have s2 : Region.Sub (kSlot p 2 (2 * p.L)) (cK p) := kSlot_sub (by omega)
  have s4 : Region.Sub (kSlot p 4 p.L) (cK p) := kSlot_sub (by omega)
  have s5 : Region.Sub (kSlot p 5 p.L) (cK p) := kSlot_sub (by omega)
  have s6 : Region.Sub (kSlot p 6 p.L) (cK p) := kSlot_sub (by omega)
  have s7 : Region.Sub (kSlot p 7 p.L) (cK p) := kSlot_sub (by omega)
  have s8 : Region.Sub (kSlot p 8 p.L) (cK p) := kSlot_sub (by omega)
  have sN : Region.Sub (kN p) (cK p) := kN_sub hf
  have kE {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (rE p) := (hf.kT.sub_left hR).sub_right rE_sub
  have kS {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (rS p) := hf.kS.sub_left hR
  have kAr {R : Region} (hR : Region.Sub R (cK p)) : R.Disjoint (kA p) := (sK.sub_left hR).sub_right kAs
  simp only [Key.keyP, callK_gpr (show Reg.r3 ∉ linkRegs by decide),
    callK_gpr (show Reg.r4 ∉ linkRegs by decide), callK_gpr (show Reg.r5 ∉ linkRegs by decide),
    callK_gpr (show Reg.r6 ∉ linkRegs by decide), callK_gpr (show Reg.r7 ∉ linkRegs by decide),
    callK_gpr (show Reg.r8 ∉ linkRegs by decide), callK_gpr (show Reg.r9 ∉ linkRegs by decide),
    callK_gpr (show Reg.r10 ∉ linkRegs by decide), r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, a2, a3, a4, a5,
    a6, a7, a8, a9, tl, t2, t8, tz, hargs, callK_sp, hu, State.withRegions_rd, State.withRegions_wr]
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
    (hf.sT.sub_right rE_sub).symm, sS.sub_right kAs,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hL1, hL2, hL3⟩, trivial, trivial, trivial, trivial, trivial, trivial, by decide, by decide, ?_⟩
  · have := p.sp.isLt
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 368).toNat = 368 from rfl]; omega),
      show (BitVec.ofNat 64 368).toNat = 368 from rfl]
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

/-! ## The key, run

`keyRun`: in a frame of its stack arguments, the key's arguments and its
call. It leaves the key's status and its outputs at the key's buffer, and
writes nothing else but the working space and the stack.
-/

/-- The key, as the controller calls it. -/
def keyCall : Prog isa := .call "vg_rsa_keygen_key" VG.Impl.RsaKeyGen.PPC64LE.Key.code

theorem keyCode_sdepth : sdepth VG.Impl.RsaKeyGen.PPC64LE.Key.code = 0 := by decide +kernel

/-- The key from the primes at the slots of `p` and `q`. -/
abbrev keyOf (p : GenPublic) (m : Mem) : Except Failure (List (List Byte)) ⊕ Unit :=
  keyOp p.L p.eB (Spec.Rsa.bytesAt m (p.slot 4) p.L) (Spec.Rsa.bytesAt m (p.slot 5) p.L)

/-- The key's outputs at the key's buffer. -/
def keyOutsOf (p : GenPublic) : List (Addr × Nat) :=
  [(p.kp, 2 * p.L), (p.slot 2, 2 * p.L), (p.slot 4, p.L), (p.slot 5, p.L), (p.slot 6, p.L), (p.slot 7, p.L),
    (p.slot 8, p.L)]

/-- What the key leaves. -/
structure AfterKey (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s t : State) : Prop where
  frame : GenFrame p original used st t
  status : ((t.gpr .r3).setWidth 32).toNat = keyStatus (keyOf p s.mem)
  out : match keyOf p s.mem with
    | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
  mem : Frame [cK p, rS p, rStk p] s.mem t.mem

section

variable {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}

theorem key_covers_writes (h : GenFrame p original used st s)
    (hw : u.wr = (allocated 176 s).wr) : Covers (kWrites p) u.wr := by
  have hf := h.input.cfacts
  have hwo := h.orig_wr
  rw [hw]
  have hin : ∀ q ∈ [cK p, rS p], q ∈ (allocated 176 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  obtain ⟨hL1, -, -⟩ := hf.len
  refine Covers.of_sub fun r hr => ?_
  simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨cK p, hin _ (by simp), 0, by simp, by simp; omega⟩
  · exact ⟨cK p, hin _ (by simp), 2 * p.L, rfl, by simp; omega⟩
  · exact ⟨cK p, hin _ (by simp), 4 * p.L, rfl, by simp; omega⟩
  · exact ⟨cK p, hin _ (by simp), 5 * p.L, rfl, by simp; omega⟩
  · exact ⟨cK p, hin _ (by simp), 6 * p.L, rfl, by simp; omega⟩
  · exact ⟨cK p, hin _ (by simp), 7 * p.L, rfl, by simp; omega⟩
  · exact ⟨cK p, hin _ (by simp), 8 * p.L, rfl, by simp; omega⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩

theorem key_covers_reads (h : GenFrame p original used st s)
    (hrd : u.rd = (allocated 176 s).rd) (hw : u.wr = (allocated 176 s).wr) :
    Covers (kReads p ++ kWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (key_covers_writes h hw).right
  have hwo := h.orig_wr
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [kReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · refine ⟨cS p, List.mem_append_right _ ?_, 48, rfl, by simp⟩
    show cS p ∈ _ :: s.wr
    rw [h.wr, hwo]; simp
  · refine ⟨⟨keySp p + 32, 144⟩, List.mem_append_right _ (by rw [alloc_key_wr h]; exact List.mem_cons_self ..),
      64, ?_, by show 64 + 80 ≤ 144; decide⟩
    show keySp p + BitVec.ofNat 64 96 = keySp p + 32 + BitVec.ofNat 64 64
    rw [BitVec.add_assoc]; rfl

theorem key_frame_sub (h : GenFrame p original used st s) :
    ∀ r ∈ [cK p, rS p, rStk p], ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  obtain ⟨hk, -, hs, -, -, -⟩ := h.regions
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨inKey original, by simp [GenInput.callChanges], by rw [hk]; exact fun _ h => h⟩
  · exact ⟨inScr original, by simp [GenInput.callChanges], by rw [hs]; exact fun _ h => h⟩
  · exact rStk_callChanges h

end

theorem key_run [InvLaw] {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (keyRun keyCall) s (AfterKey p original used st s) := by
  have hf := h.input.cfacts
  have hspn : s.sp.toNat = p.sp.toNat - 192 := by
    have hF := h.input.F_toNat
    have hr := hf.room
    have hsu : stackUse = 1088 := rfl
    rw [h.sp, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (80 : BitVec 64).toNat = 80 from rfl]; omega),
      show (80 : BitVec 64).toNat = 80 from rfl, hF]
    omega
  have hroom : 176 ≤ s.sp.toNat := by have := hf.room; have hsu : stackUse = 1088 := rfl; omega
  unfold keyRun keyCall
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (WP.mono (key_stack_ok h) fun u ⟨⟨hm, ku⟩, hyu⟩ => ?_)
  refine WP.seq (WP.mono (key_args_ok h hm ku) fun w ⟨⟨⟨ha, hmw⟩, kw⟩, hyw⟩ => ?_)
  have hu : w.sp = keySp p := kw.sp.trans (ku.sp.trans (alloc_key_sp h))
  have hm' : w.mem = keyMem p s := hmw.trans hm
  have krd : w.rd = (allocated 176 s).rd := kw.rd.trans ku.rd
  have kwr : w.wr = (allocated 176 s).wr := kw.wr.trans ku.wr
  refine VG.PPC64LE.WP.of_syms (WP.callAny (k := Key.keyP) (fun s' h' => Key.key_correct s' h')
    (callK_pre h hu ha hm') (key_covers_reads h krd kwr) (key_covers_writes h kwr) ?_
    (by rw [keyCode_sdepth]; decide))
  intro t htr htw hsp hfr hcs hpost hyt
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := callK_args (s := s) hu hm'
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have hcf : Frame [cStack p] s.mem w.mem := by
    rw [hm']
    exact (key_low_frame h).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_singleton_self _, rStk_sub p⟩
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -⟩ := hst
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt w.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hcf.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR]
  have hres : Key.resOf (callK p w) = keyOf p s.mem := by
    simp only [Key.resOf, callK_gpr (show Reg.r7 ∉ linkRegs by decide),
      callK_gpr (show Reg.r8 ∉ linkRegs by decide), callK_gpr (show Reg.r9 ∉ linkRegs by decide), r7, r8, r9,
      tl, a6, a7, callK_mem, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide),
      hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega),
      hbytes (R := ⟨p.slot 5, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega)]
    have he : Spec.Rsa.bytesAt s.mem (p.stp + BitVec.ofNat 64 48) 8 = p.eB := h.state.e
    rw [he]
  have hregs : ∀ m : Mem, Key.outBytes (callK p w) m =
      (keyOutsOf p).map fun o => Spec.Rsa.bytesAt m o.1 o.2 := by
    intro m
    simp only [Key.outBytes, callK_gpr (show Reg.r3 ∉ linkRegs by decide),
      callK_gpr (show Reg.r4 ∉ linkRegs by decide), callK_gpr (show Reg.r5 ∉ linkRegs by decide),
      callK_gpr (show Reg.r7 ∉ linkRegs by decide), callK_gpr (show Reg.r8 ∉ linkRegs by decide),
      callK_gpr (show Reg.r9 ∉ linkRegs by decide), r3, r4, r5, r7, r8, r9, tl, t2, a0, a2, a4]
    rfl
  obtain ⟨hstat, hout⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem] at hstat hout
  rw [hres] at hstat hout
  -- The memory: the stack arguments, then the key.
  have mK : cK p ∈ [cK p, rS p, rStk p] := List.mem_cons_self ..
  have mS : rS p ∈ [cK p, rS p, rStk p] := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have mT : rStk p ∈ [cK p, rS p, rStk p] := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f₀ : Frame [cK p, rS p, rStk p] s.mem w.mem := by
    rw [hm']
    exact (key_low_frame h).sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨_, mT, fun _ h => h⟩
  have f₁ : Frame [cK p, rS p, rStk p] w.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cK p, mK, kN_sub hf⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨rS p, mS, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, mT, fun x hx => ?_⟩
      rw [keyCode_sdepth] at hx
      simp only [Region.Contains] at hx
      omega
  have hframe := f₀.trans f₁
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d := by
    refine hframe.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega)) (fun q hq => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (rStk_sub p)
  refine ⟨h.restore (show t.rd = s.rd from htr.trans krd)
      (show t.wr.tail = s.wr by rw [htw, kwr]; rfl) ?_ (hyt.trans (hyw.trans hyu))
      (fun r hr => (hcs r hr).trans ((kw.gpr r (by revert r hr; decide)).trans (ku.gpr r (by revert r hr; decide))))
      (hframe.sub (key_frame_sub h)) ((hword 0 (by decide)).trans h.state.remaining)
      ((hword 8 (by decide)).trans h.state.len) ((hword 16 (by decide)).trans h.state.cap) (.inl rfl) rfl
      h.state.remaining_le, hstat, ?_, hframe⟩
  · show t.sp + BitVec.ofNat 64 176 = s.sp
    rw [hsp, hu, ← alloc_key_sp h]
    exact BitVec.sub_add_cancel _ _
  · show match keyOf p s.mem with
      | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
      | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
    revert hout
    rcases keyOf p s.mem with (_ | ys) | _
    · intro hz
      simp only [Key.outZero, callK_gpr (show Reg.r3 ∉ linkRegs by decide),
        callK_gpr (show Reg.r4 ∉ linkRegs by decide), callK_gpr (show Reg.r5 ∉ linkRegs by decide),
        callK_gpr (show Reg.r7 ∉ linkRegs by decide), callK_gpr (show Reg.r8 ∉ linkRegs by decide),
        callK_gpr (show Reg.r9 ∉ linkRegs by decide), r3, r4, r5, r7, r8, r9, tl, t2, a0, a2, a4] at hz
      obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := hz
      intro o ho
      simp only [keyOutsOf, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [z0, z1, z2, z3, z4, z5, z6]
    · intro hy; rw [← hregs]; exact hy
    · intro hz
      simp only [Key.outZero, callK_gpr (show Reg.r3 ∉ linkRegs by decide),
        callK_gpr (show Reg.r4 ∉ linkRegs by decide), callK_gpr (show Reg.r5 ∉ linkRegs by decide),
        callK_gpr (show Reg.r7 ∉ linkRegs by decide), callK_gpr (show Reg.r8 ∉ linkRegs by decide),
        callK_gpr (show Reg.r9 ∉ linkRegs by decide), r3, r4, r5, r7, r8, r9, tl, t2, a0, a2, a4] at hz
      obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := hz
      intro o ho
      simp only [keyOutsOf, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [z0, z1, z2, z3, z4, z5, z6]

end VG.Proof.RsaKeyGen.PPC64LE.Generate

/-! ## The controller's loop (PPC64LE)

After a prime's search: the count of the octets it consumed (`Mid`), then
the key search asks for more entropy, ends, or goes on to the next prime's
search, to a state of a lower measure; the loop ends with the key search's
result.
-/

namespace VG.Proof.RsaKeyGen.PPC64LE.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.RsaKeyGen.PPC64LE.Search (WP.keepS)

/-! ## The loop's states -/

/-- A loop state that ended the key search with `final`: the frame for its
consumption and its state for the next call, its status in the frame, the
key's buffer, and its request in the state. -/
def GenDone (p : GenPublic) (original : State) (final : KeySearchResult) (s : State) : Prop :=
  GenFrame p original final.used final.progress s ∧ word s.mem p.F 80 = BitVec.ofNat 64 final.keyStatus ∧
    Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final ∧
    ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested

/-- What each step that goes on lowers: the octets left of the tape, then the
generations left. -/
def genMeasure (p : GenPublic) (used : Nat) (st : KeyProgress) : Nat := (p.randLen - used) * 2 ^ 64 + st.left

/-- The loop's invariant, at the measure `n`. -/
def GenInv (p : GenPublic) (original : State) (final : KeySearchResult) (n : Nat) (s : State) : Prop :=
  ∃ used st, n = genMeasure p used st ∧ GenIter p original final used st s

/-- What a prime's search leaves: its prime's octets, or zeros. -/
def outBytes (L : Nat) (r : PrimeSearchResult) : List Byte :=
  match r.outcome with
  | .accepted c => Spec.Rsa.i2osp c L
  | _ => List.replicate L 0

/-- The search of the progress' prime from octet `used`. -/
abbrev rOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : PrimeSearchResult :=
  primeOf p.L p.eB st ((genRand original).drop used)

/-- After a search and the count of the octets it consumed. -/
structure Mid (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (u : State) : Prop where
  frame : GenFrame p original (used + (rOf p original used st).used)
    ⟨st.left, st.phase, (rOf p original used st).remaining⟩ u
  final : ∃ tr, final = (tailOf p original used st).consume used tr
  low : Spec.Rsa.bytesAt u.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0
  slot4 : Spec.Rsa.bytesAt u.mem (p.slot 4) p.L =
    (match st.phase with
      | .p => outBytes p.L (rOf p original used st)
      | .q pB => pB)
  slot5 : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L =
    (match st.phase with
      | .p => List.replicate p.L 0
      | .q _ => outBytes p.L (rOf p original used st))
  high : Spec.Rsa.bytesAt u.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0
  req : ∃ requested, word u.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (rOf p original used st).Requests (primeEntropy p.L) requested

/-! ## The key's buffer -/

theorem bytesAt_add (m : Mem) (a : Addr) (x y : Nat) :
    Spec.Rsa.bytesAt m a (x + y) = Spec.Rsa.bytesAt m a x ++ Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.ofNat_add, BitVec.add_assoc]

/-- The key's buffer, as the key's outputs. -/
theorem key_outs (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) =
      ((keyOutsOf p).map fun o => Spec.Rsa.bytesAt m o.1 o.2).flatten := by
  simp only [keyOutsOf, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show 9 * p.L = 2 * p.L + 2 * p.L + p.L + p.L + p.L + p.L + p.L by omega]
  rw [bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    show 2 * p.L + 2 * p.L = 4 * p.L by omega, show 4 * p.L + p.L = 5 * p.L by omega,
    show 5 * p.L + p.L = 6 * p.L by omega, show 6 * p.L + p.L = 7 * p.L by omega,
    show 7 * p.L + p.L = 8 * p.L by omega]
  simp only [List.append_assoc]

/-- The key's buffer: the low four slots, `p`'s, `q`'s and the high three. -/
theorem key_bytes (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) = Spec.Rsa.bytesAt m p.kp (4 * p.L) ++
      Spec.Rsa.bytesAt m (p.slot 4) p.L ++ Spec.Rsa.bytesAt m (p.slot 5) p.L ++
      Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) := by
  rw [show 9 * p.L = 4 * p.L + p.L + p.L + 3 * p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]

/-! ## After the search -/

section

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- A region of the key's buffer apart from the search's output is kept
through the search. -/
theorem search_kept (h : GenLive p original used st s) (hm : Frame (searchChanges p st) s.mem t.mem)
    {R : Region} (hR : Region.Sub R (cK p)) (hO : R.Disjoint (rO p st)) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have hf := h.input.cfacts
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, -, -⟩ := hst
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine hm.bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hO
  · exact hf.kU.sub_left hR
  · exact hf.kS.sub_left hR
  · exact (hf.kT.sub_left hR).sub_right rT_sub
  · exact (sK.sub_left hR).sub_right (rStk_sub p)

theorem genRand_length (h : GenFrame p original used st s) : (genRand original).length = p.randLen := by
  rw [← h.random]; simp [Spec.Rsa.bytesAt]

theorem rOf_used_le (h : GenFrame p original used st s) : used + (rOf p original used st).used ≤ p.randLen := by
  have h2 : (rOf p original used st).used ≤ p.randLen - used := by
    have := primeSearch_used_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
    rw [List.length_drop, genRand_length h] at this
    exact this
  have := h.used_le
  omega

/-- The key's buffer and the state's request through the count of the octets
consumed. -/
theorem head_kept (h : GenFrame p original used st s) {u : State} {v : BitVec 64}
    (hm : u.mem = writeFrame s.mem p.F [(8, v)]) {R : Region} (hR : Region.Sub R (cK p)) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  rw [hm]
  exact bytes_kept (writeFrame_frame14 _ _ _ fun e he => by
    obtain rfl := List.mem_singleton.mp he; show 8 < 14; decide) (h.frame_key.sub_right hR) hn

theorem slot_disj (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.slot i, a⟩ : Region).Disjoint ⟨p.slot j, b⟩ := kk hf h ha hb

theorem low_disj (hf : CFacts p) {j b : Nat} (h : 4 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.kp, 4 * p.L⟩ : Region).Disjoint ⟨p.slot j, b⟩ := by
  have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

end

theorem prime_status_lt (r : PrimeSearchResult) : r.status < 4 := by
  show r.outcome.status < 4
  cases r.outcome <;> simp [Spec.Entropy.Outcome.status]

/-- The status and the count of the octets consumed, after the search. -/
theorem after_head {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (.block [.lsr .w .r3 .r3 0, ldf .r11 2, .load .d .r11 .r11 0, ldf .r12 8, .add .r12 .r12 .r11,
      stf .r12 8]) t fun u =>
      u.gpr .r3 = BitVec.ofNat 64 (rOf p original used st).status ∧
        u.gpr .r11 = BitVec.ofNat 64 (rOf p original used st).used ∧ Mid p original final used st u := by
  obtain ⟨hl, hfin⟩ := hi
  have hf := hl.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := rOf_used_le hl.toGenFrame
  refine WP.mono (head_ok ha.frame (prime_status_lt _) ha.status ha.usedw)
    fun u ⟨⟨⟨hax, hcx, hm⟩, k⟩, hy⟩ => ⟨hax, hcx, ?_⟩
  rw [SearchInit.add_ofNat] at hm
  have hb : ∀ e ∈ [(8, BitVec.ofNat 64 (used + (rOf p original used st).used))], e.1 < 14 := by
    intro e he; obtain rfl := List.mem_singleton.mp he; show 8 < 14; decide
  have hhead : ∀ {R : Region}, Region.Sub R (cK p) → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt t.mem R.base R.len :=
    fun hR hn => head_kept ha.frame hm hR hn
  have hkey := hl.key
  have hlow : Spec.Rsa.bytesAt t.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [← hkey.low]
    refine search_kept hl ha.mem (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) ?_ (by
      show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact low_disj hf (by decide) (by omega)
    · exact low_disj hf (by decide) (by omega)
  have hsplit : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) =
      Spec.Rsa.bytesAt s.mem (p.slot 5) p.L ++ Spec.Rsa.bytesAt s.mem (p.slot 6) (3 * p.L) := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add, slot_succ]
  have hhigh5 := hkey.high
  rw [hsplit, show 4 * p.L = p.L + 3 * p.L by omega, ← List.replicate_append_replicate] at hhigh5
  obtain ⟨h5s, h6s⟩ := List.append_inj hhigh5 (by simp [Spec.Rsa.bytesAt]) |>.imp id id
  have hhigh : Spec.Rsa.bytesAt t.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0 := by
    rw [← h6s]
    refine search_kept hl ha.mem (R := ⟨p.slot 6, 3 * p.L⟩) (kSlot_sub (by omega)) ?_ (by
      show 3 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact slot_disj hf (by omega) (by omega) (by omega)
    · exact slot_disj hf (by omega) (by omega) (by omega)
  have hout := ha.out
  have hs4 : Spec.Rsa.bytesAt t.mem (p.slot 4) p.L =
      (match st.phase with
        | .p => outBytes p.L (rOf p original used st)
        | .q pB => pB) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      have ho : outOf p ⟨left, .p, remaining⟩ = p.slot 4 := rfl
      rw [ho] at hout
      rw [hout]; rfl
    | q pB =>
      rw [← hkey.other pB rfl]
      exact search_kept hl ha.mem (R := ⟨p.slot 4, p.L⟩) (kSlot_sub (by omega))
        (slot_disj hf (by omega) (by omega) (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
  have hs5 : Spec.Rsa.bytesAt t.mem (p.slot 5) p.L =
      (match st.phase with
        | .p => List.replicate p.L 0
        | .q _ => outBytes p.L (rOf p original used st)) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      rw [← h5s]
      exact search_kept hl ha.mem (R := ⟨p.slot 5, p.L⟩) (kSlot_sub (by omega))
        (slot_disj hf (by omega) (by omega) (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
    | q pB =>
      have ho : outOf p ⟨left, .q pB, remaining⟩ = p.slot 5 := rfl
      rw [ho] at hout
      rw [hout]; rfl
  obtain ⟨req, hreq, hreqs⟩ := ha.req
  refine ⟨ha.frame.store hle _ hb (by intro e he; obtain rfl := List.mem_singleton.mp he; show 9 ≠ 8; decide) hm
      k.rd k.wr k.sp hy (fun r hr => k.gpr r (by revert r hr; decide))
      (by rw [hm]; exact slots_used ha.frame _ [] (by simp) (by simp)),
    hfin, ?_, ?_, ?_, ?_, ⟨req, ?_, hreqs⟩⟩
  · rw [hhead (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) (by show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hlow
  · rw [hhead (R := ⟨p.slot 4, p.L⟩) (kSlot_sub (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hs4
  · rw [hhead (R := ⟨p.slot 5, p.L⟩) (kSlot_sub (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hs5
  · rw [hhead (R := ⟨p.slot 6, 3 * p.L⟩) (kSlot_sub (by omega)) (by show 3 * p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hhigh
  · rw [hm]
    refine Eq.trans ((writeFrame_frame14 _ _ _ hb).readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hreq
    obtain rfl := List.mem_singleton.mp hq
    exact ha.frame.state_frame.symm

theorem Mid.keepK {p : GenPublic} {original u v : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (h : Mid p original final used st u) {rs : List Reg} (k : Keep rs u v)
    (hm : v.mem = u.mem) (hy : v.syms = u.syms) (hrs : ∀ r ∈ preserved, r ∉ rs) :
    Mid p original final used st v := by
  refine ⟨h.frame.keepK k hm hy hrs, h.final, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.low, h.slot4, h.slot5, h.high, h.req]

/-! ## How a step ends -/

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

/-- `clearAll`: zeros at the whole key's buffer. -/
theorem clearAll_ok (h : GenFrame p original used st s) :
    WP isa clearAll s fun t => GenFrame p original used st t ∧
      Spec.Rsa.bytesAt t.mem p.kp (9 * p.L) = List.replicate (9 * p.L) 0 ∧
      Frame [cK p, p.frame] s.mem t.mem := by
  have hn := h.key_nowrap
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have hkr := h.key_region
  have h9 : BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L = BitVec.ofNat 64 (9 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]; congr 1; omega
  unfold clearAll
  refine WP.seq (WP.mono (setAll_ok h) fun t1 ⟨⟨hm1, k1⟩, hy1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 hy1 (by decide)
  rw [h9] at w13
  refine WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega)) (by omega) (by omega)
    (by omega)) fun t2 ⟨g2, z2, f2, _, _⟩ => ⟨g2, bytes_zero z2, ?_⟩
  refine (f1.sub fun r hr => ?_).trans (f2.sub fun r hr => ?_)
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp, fun _ h => h⟩
  · obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩

end

/-- The state's word `j` through stores to the state and the frame. -/
theorem stores_word {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv)
    (j : Nat) (hj : j < 7) :
    word (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.stp (8 * j) =
      frameValue sv j (word s.mem p.stp (8 * j)) := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 14 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hnst : p.stp.toNat + 56 ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inState original) (by simp [inWrites])
    rwa [h.state_region] at this
  rw [← writeFrame_word _ _ _ hsb j (by omega)]
  exact (writeFrame_frame14 _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
    (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact h.state_frame.symm) (by decide)

/-- The key's buffer through stores to the state and the frame. -/
theorem stores_key {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv)
    {j n : Nat} (hj : j * p.L + n ≤ 9 * p.L) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) (p.kp + BitVec.ofNat 64 (j * p.L)) n =
      Spec.Rsa.bytesAt s.mem (p.kp + BitVec.ofNat 64 (j * p.L)) n := by
  have hf := h.input.cfacts
  refine stores_bytes p s.mem (R := ⟨p.kp + BitVec.ofNat 64 (j * p.L), n⟩) hv ?_ ?_ (by have := hf.nK; simp; omega)
  · exact (hf.kT.symm.sub_right (slot_sub _ hj)).sub_left (Region.sub_prefix (by decide))
  · exact h.frame_key.sub_right (slot_sub _ hj)

theorem stores_key9 {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.kp (9 * p.L) =
      Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) := by
  have := stores_key h hv (j := 0) (n := 9 * p.L) (by omega)
  rwa [Nat.zero_mul, ← kp_zero] at this

/-- `finishWith status`: the key search ended with `final`. -/
theorem finish_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0)
    (hkey : Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (.block (finishWith status)) s (GenDone p original final) := by
  refine WP.mono (finishWith_ok h hstat) fun t ⟨⟨hm, k⟩, hy⟩ => ?_
  have hv : StateStores [(4, BitVec.ofNat 64 0), (5, BitVec.ofNat 64 0)] [(10, BitVec.ofNat 64 status)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have h0 := h.state.remaining
  rw [hr0] at h0
  have hg : GenFrame p original u ⟨0, .p, 0⟩ t :=
    h.setState hv hm k.rd k.wr k.sp hy (fun r hr => k.gpr r (by revert r hr; decide)) h0 rfl rfl
      (Nat.zero_le _) (by decide)
  obtain ⟨req, hw, hr⟩ := hreq
  refine ⟨by rw [hu, hpr]; exact hg, ?_, ?_, ⟨req, ?_, hr⟩⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide), hs]
    rfl
  · rw [hm, stores_key9 h hv, hkey]
  · rw [hm]
    exact (stores_word h hv 3 (by decide)).trans hw

/-- The start of the next prime's search, for the progress `st'`: a loop
state, its status 4. -/
theorem cont_of {p : GenPublic} {original s t : State} {u : Nat} {st st' : KeyProgress}
    (h : GenFrame p original u st s) {sv : List (Nat × BitVec 64)}
    (hv : StateStores sv [(10, BitVec.ofNat 64 4)])
    (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F [(10, BitVec.ofNat 64 4)])
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) (hy : t.syms = s.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = s.gpr r)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64)
    (hlow : Spec.Rsa.bytesAt s.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0)
    (hhigh : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hother : ∀ pB, st'.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB)
    (hreq : word s.mem p.stp 24 = BitVec.ofNat 64 0) :
    word t.mem p.F 80 = BitVec.ofNat 64 4 ∧ GenLive p original u st' t ∧
      word t.mem p.stp 24 = BitVec.ofNat 64 0 := by
  obtain ⟨hL1, -, -⟩ := h.len_valid
  have hg' := h.setState hv hm hr hw hsp hy hg h0 h4 h5 hrem hlt
  have h3 : ∀ e ∈ sv, 3 ≠ e.1 := fun e he heq => by rcases hv.1 e he with h | h | h <;> omega
  refine ⟨?_, ⟨hg', ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; decide) 10 (by decide)]
    rfl
  · have := stores_key h hv (j := 0) (n := 4 * p.L) (by omega)
    rw [Nat.zero_mul, ← kp_zero] at this
    rw [hm, this, hlow]
  · rw [hm, stores_key h hv (j := 5) (n := 4 * p.L) (by omega), hhigh]
  · intro pB hpB
    rw [hm, stores_key h hv (j := 4) (n := p.L) (by omega), hother pB hpB]
  · rw [hm]
    exact (stores_word h hv 3 (by decide)).trans ((frameValue_unchanged _ _ _ h3).trans hreq)

/-! ## A prime's search that asked for entropy or was exhausted -/

/-- How the key search goes on after the prime's search `r` from the progress
`st`: to the progress `st'`, with `e` this step's trace. -/
def NextPub (st : KeyProgress) (r : PrimeSearchResult) (st' : KeyProgress) (e : List Nat) : Prop :=
  (r.outcome = .exhausted ∧ st'.left = st.left - 1 ∧ st'.phase = .p ∧ e = primeEntry r) ∨
  (∃ c, r.outcome = .accepted c ∧ st.phase = .p ∧ st'.left = st.left ∧ phaseWord st'.phase = 1 ∧
    e = primeEntry r) ∨
  (∃ c pB, r.outcome = .accepted c ∧ st.phase = .q pB ∧ st'.left = st.left ∧ st'.phase = .p ∧
    e = primeEntry r ++ [1, 2])

/-- After a step that goes on: its status 4, and the loop state of the next
prime's search, of a lower measure. -/
structure Cont (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop where
  status : word t.mem p.F 80 = BitVec.ofNat 64 4
  req : word t.mem p.stp 24 = BitVec.ofNat 64 0
  next : ∃ st' e, GenLive p original (used + (rOf p original used st).used) st' t ∧
    genMeasure p (used + (rOf p original used st).used) st' < genMeasure p used st ∧
    tailOf p original used st =
      (tailOf p original (used + (rOf p original used st).used) st').consume (rOf p original used st).used e ∧
    st'.remaining = limitOf p.L p.eB ∧ NextPub st (rOf p original used st) st' e
  final : ∃ tr, final = (tailOf p original used st).consume used tr

/-- Whether the key search goes on after the prime's search from `st`. -/
def ContSpec (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : Prop :=
  ((rOf p original used st).outcome = .exhausted ∧ ¬st.left ≤ 1) ∨
  (∃ c, (rOf p original used st).outcome = .accepted c ∧ (rOf p original used st).used ≠ 0 ∧
    (st.phase = .p ∨ ∃ pB, st.phase = .q pB ∧ keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) = .inr ()))

/-- After a step: the next prime's search, or the key search ended with
`final`. -/
def Classified (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  (ContSpec p original used st ∧ Cont p original final used st t) ∨
    (¬ContSpec p original used st ∧ GenDone p original final t)

/-- `fail status`: zeros at the key's buffer, and the key search ended with
`final`. -/
theorem fail_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0) (hz : keySearchBytes p.L final = List.replicate (9 * p.L) 0)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (fail status) s (GenDone p original final) := by
  have hf := h.input.cfacts
  unfold fail
  refine WP.seq (WP.mono (clearAll_ok h) fun w ⟨g, z, fr⟩ => ?_)
  obtain ⟨req, hw, hr⟩ := hreq
  refine finish_done g hstat hu hpr hs hr0 (z.trans hz.symm) ⟨req, ?_, hr⟩
  refine Eq.trans (fr.readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
    (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
    (fun q hq => ?_) (by decide)) hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hf.kT.symm
  · exact h.state_frame.symm

theorem rOf_status (r : PrimeSearchResult) : r.status = r.outcome.status := rfl

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- The search asked for more entropy: so does the key search. -/
theorem classify_entropy (hm : Mid p original final used st u)
    (hax : u.gpr .r3 = BitVec.ofNat 64 (rOf p original used st).status) {k a : Nat}
    (ho : (rOf p original used st).outcome = .entropy k a) :
    WP isa (.block [stf .r3 10]) u (Classified p original final used st) := by
  have hs0 : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
  have hrem : (rOf p original used st).remaining = k := by
    simp only [PrimeSearchResult.remaining, ho]
  rw [hs0] at hax
  have hframe := hm.frame
  rw [hrem] at hframe
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_entropy (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
  have hfinal : final = ⟨.entropy ⟨st.left, st.phase, k⟩ a, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  refine WP.mono (storeStatus_ok hframe hax) fun t ⟨⟨htm, k'⟩, hy⟩ => Or.inr ⟨?_, ?_⟩
  · rintro (⟨h, -⟩ | ⟨c, h, -⟩) <;> rw [ho] at h <;> cases h
  have hv : StateStores [] [(10, BitVec.ofNat 64 0)] := by
    constructor
    · simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hg : GenFrame p original (used + (rOf p original used st).used) ⟨st.left, st.phase, k⟩ t :=
    hframe.setState hv htm k'.rd k'.wr k'.sp hy (fun r _ => k'.gpr r (by simp)) hframe.state.remaining
      hframe.state.phase hframe.state.left hframe.state.remaining_le hframe.state.left_lt
  obtain ⟨req, hw, hr⟩ := hm.req
  subst hfinal
  refine ⟨hg, ?_, ?_, ⟨req, ?_, ?_⟩⟩
  · rw [htm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide)]
    rfl
  · rw [htm, stores_key9 hframe hv, key_bytes, hm.low, hm.slot4, hm.slot5, hm.high]
    have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
      simp only [outBytes, ho]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only [hout, keySearchBytes, List.replicate_append_replicate]
      congr 1; omega
    | q pB =>
      simp only [hout, keySearchBytes, List.append_assoc, List.replicate_append_replicate]
      congr 3; omega
  · rw [htm]; exact (stores_word hframe hv 3 (by decide)).trans hw
  · simp only [Spec.Entropy.Result.Requests, ho] at hr ⊢
    exact hr

/-- The search was exhausted, and so is the key search: its last generation. -/
theorem classify_last (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : st.left ≤ 1) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_last (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho hl
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- The search was exhausted: the next generation, from `p`. -/
theorem classify_next (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : ¬st.left ≤ 1) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
      (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, BitVec.ofNat 64 4)])
    (hr : t.rd = u.rd) (hw : t.wr = u.wr) (hsp : t.sp = u.sp) (hy : t.syms = u.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = u.gpr r) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hks := ks_exhausted_next (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho hl
  have hv : StateStores [(5, BitVec.ofNat 64 (st.left - 1)), (0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 0)] [(10, BitVec.ofNat 64 4)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
    simp only [outBytes, ho]
  have hle := hm.frame.used_le
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add, slot_succ, hm.slot5, hm.high,
      ← List.replicate_append_replicate]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => rfl
    | q pB => simp only [hout]
  have hreq0 : word u.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [hw', this]
  obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left - 1, .p, limitOf p.L p.eB⟩) hm.frame hv htm hr hw hsp hy hg
    rfl rfl rfl (Nat.le_refl _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hm.frame.state.left_lt) hm.low hhigh5
    (fun _ h => by cases h) hreq0
  refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st), hlive, ?_, ?_, rfl, .inl ⟨ho, rfl, rfl, rfl⟩⟩, hm.final⟩
  · unfold genMeasure
    dsimp only
    have hmul : (p.randLen - (used + (rOf p original used st).used)) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [tailOf, hks, tailOf, List.drop_drop]

end

/-! ## A generation exhausted, or a prime accepted -/

/-- One generation fewer, and the next prime's search from `p`. -/
theorem dec_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (h12 : s.gpr .r12 = p.stp)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 st.left) (hl : 2 ≤ st.left) :
    WP isa (.block (([.subi .r11 .r11 1, .store .d .r11 .r12 40] : List Instr) ++ nextPrime 0)) s fun t =>
      (t.mem = writeFrame (writeFrame s.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
        (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, BitVec.ofNat 64 4)] ∧
        Keep [.r11, .r12] s t) ∧ t.syms = s.syms := by
  have hsf := h.frame_st
  have sst := h.stateScr
  have h7 := h.slot (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11v := h.slot (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7 h11v
  have hs0 : InRegions s.wr (p.stp + BitVec.ofNat 64 0) 8 := sst.st (d := 0) (n := 8) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (n := 8) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (n := 8) (by decide)
  have hlt := h.state.left_lt
  have hsub : BitVec.ofNat 64 st.left - BitVec.ofNat 64 1 = BitVec.ofNat 64 (st.left - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show st.left - 1 < 2 ^ 64 by omega)]
    omega
  have hnF : p.F.toNat + 112 ≤ 2 ^ 64 := (h.input.frame_scr h.wr).nowrap
  have hnS : p.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 112) :
      (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 d) 64 =
        s.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨p.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega))).readW (r := p.frame)
      (Offset.contains_base _ hd (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact h.state_frame) (by decide)
  have hk7 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 56) 64 =
      p.stp := fun v => (hkeep v 56 (by decide)).trans h7
  have hk11 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 88) 64 =
      BitVec.ofNat 64 (limitOf p.L p.eB) := fun v => (hkeep v 88 (by decide)).trans h11v
  have hst5 : (Mem.writeW s.mem (p.stp + BitVec.ofNat 64 40) (BitVec.ofNat 64 (st.left - 1))) =
      s.mem.writeW (p.stp + BitVec.ofNat 64 (8 * 5)) (BitVec.ofNat 64 (st.left - 1)) := rfl
  refine WP.keepS [.r11, .r12] ?_ (by decide)
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]
  prun [ldf, stf, h.r31, h12, h11, hsub, exec_subi (show Reg.r11 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide),
    h.frame_ld 56 (by decide), h.frame_ld 88 (by decide), hk7, hk11, hs0, hs4, hs5, hsf 80 (by decide),
    exec_li (show 0 < 2 ^ 15 by decide), exec_li (show 4 < 2 ^ 15 by decide), off]

theorem drop_lt {rest : List Byte} {n : Nat} (h0 : 0 < n) (hn : n ≤ rest.length) :
    (rest.drop n).length < rest.length := by
  rw [List.length_drop]; omega

theorem measure_lt (p : GenPublic) {used n : Nat} {st st' : KeyProgress} (h0 : 0 < n)
    (hn : used + n ≤ p.randLen) (hl : st'.left ≤ st.left) :
    genMeasure p (used + n) st' < genMeasure p used st := by
  unfold genMeasure
  have hmul : (p.randLen - (used + n) + 1) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- `exhaustedGen`: the key search exhausted, or the next generation. -/
theorem classify_exhausted (hm : Mid p original final used st u)
    (ho : (rOf p original used st).outcome = .exhausted) :
    WP isa exhaustedGen u (Classified p original final used st) := by
  unfold exhaustedGen
  refine WP.seq (WP.mono (left_ok hm.frame) fun v ⟨⟨⟨hb, h12, h11, hmem⟩, k⟩, hy⟩ => ?_)
  have hv := hm.keepK k hmem hy (fun r hr => by revert r; decide)
  refine WP.ite (decide (st.left ≤ 1)) hb (fun hl => ?_) (fun hl => ?_)
  · refine WP.mono (classify_last hv ho (of_decide_eq_true hl)) fun _ h => Or.inr ⟨?_, h⟩
    rintro (⟨-, h⟩ | ⟨c, h, -⟩)
    · exact h (of_decide_eq_true hl)
    · rw [ho] at h; cases h
  · have hl' := of_decide_eq_false hl
    refine WP.mono (dec_ok hv.frame h12 h11 (by show 2 ≤ st.left; omega)) fun t ⟨⟨htm, k2⟩, hy2⟩ =>
      Or.inl ⟨.inl ⟨ho, hl'⟩, ?_⟩
    exact classify_next hv ho hl' htm k2.rd k2.wr k2.sp hy2 (fun r hr => k2.gpr r (by revert r hr; decide))

/-- A prime accepted having read nothing: the key search is exhausted. -/
theorem classify_none (hm : Mid p original final used st u) {c : Nat}
    (ho : (rOf p original used st).outcome = .accepted c) (h0 : (rOf p original used st).used = 0) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_accepted_none (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by show ¬(List.drop (rOf p original used st).used _).length < _; rw [h0, List.drop_zero]; omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- `p` accepted: `q` next. -/
theorem classify_p (hm : Mid p original final used st u) {c : Nat}
    (ho : (rOf p original used st).outcome = .accepted c) (hpos : 0 < (rOf p original used st).used)
    (hph : st.phase = .p) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 1)]) p.F [(10, BitVec.ofNat 64 4)])
    (hr : t.rd = u.rd) (hw : t.wr = u.wr) (hsp : t.sp = u.sp) (hy : t.syms = u.syms)
    (hg : ∀ r ∈ preserved, t.gpr r = u.gpr r) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hks := ks_accepted_p (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (drop_lt hpos hrest) hph
  have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 1)]
      [(10, BitVec.ofNat 64 4)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs4
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add, slot_succ, hs5, hm.high,
      ← List.replicate_append_replicate]
  have hreq0 : word u.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [hw', this]
  obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left, .q (Spec.Rsa.i2osp c p.L), limitOf p.L p.eB⟩) hm.frame
    hv htm hr hw hsp hy hg rfl rfl hm.frame.state.left (Nat.le_refl _) hm.frame.state.left_lt hm.low hhigh5
    (fun pB h => by cases h; exact hs4) hreq0
  refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st), hlive, measure_lt p hpos hle (Nat.le_refl _), ?_, rfl,
    .inr (.inl ⟨c, ho, hph, rfl, rfl, rfl⟩)⟩, hm.final⟩
  rw [tailOf, hks, tailOf, List.drop_drop]

end

/-! ## The key from `p` and `q` -/

theorem sub_ofNat_beq {n c : Nat} (hn : n < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 c == 0) = decide (n = c) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hc,
      show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega
  · rintro rfl; exact BitVec.sub_self _

/-- The key's status, its low 32 bits, compared with 1. -/
theorem key_status_guard {s : State} {status : Nat} (hs : ((s.gpr .r3).setWidth 32).toNat = status)
    (hst : status < 4) :
    WP isa (.block [.lsr .w .r3 .r3 0, .subi .r11 .r3 1]) s fun t =>
      ((isa.eval (.zero .d .r11) t = some (decide (status = 1)) ∧ t.gpr .r3 = BitVec.ofNat 64 status ∧
        t.mem = s.mem) ∧ Keep [.r3, .r11] s t) ∧ t.syms = s.syms := by
  have h0 : (s.gpr .r3).setWidth 32 = BitVec.ofNat 32 status := by
    apply BitVec.eq_of_toNat_eq
    rw [hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb := sub_ofNat_beq (n := status) (c := 1) (by omega) (by decide)
  refine WP.keepS [.r3, .r11] ?_ (by decide)
  prun [exec_lsr_w (show 0 < 32 by decide), h0, Search.zext32 (show status < 2 ^ 32 by omega),
    exec_subi (show Reg.r3 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hb]

/-- A status in `r3`, compared with `c` into `d`. -/
theorem sub_guard3_r11 {s : State} {status : Nat} (hs : s.gpr .r3 = BitVec.ofNat 64 status)
    (hst : status < 2 ^ 64) :
    WP isa (.block [.subi .r11 .r3 2]) s fun t =>
      ((isa.eval (.zero .d .r11) t = some (decide (status = 2)) ∧ t.mem = s.mem) ∧ Keep [.r11] s t) ∧
        t.syms = s.syms := by
  have hb := sub_ofNat_beq (n := status) (c := 2) hst (by decide)
  refine WP.keepS [.r11] ?_ (by decide)
  prun [hs, exec_subi (show Reg.r3 ≠ .r0 by decide) (show 2 ≤ 2 ^ 15 by decide)]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hb]

theorem sub_guard3_r12 {s : State} {status : Nat} (hs : s.gpr .r3 = BitVec.ofNat 64 status)
    (hst : status < 2 ^ 64) :
    WP isa (.block [.subi .r12 .r3 3]) s fun t =>
      ((isa.eval (.zero .d .r12) t = some (decide (status = 3)) ∧ t.mem = s.mem) ∧ Keep [.r12] s t) ∧
        t.syms = s.syms := by
  have hb := sub_ofNat_beq (n := status) (c := 3) hst (by decide)
  refine WP.keepS [.r12] ?_ (by decide)
  prun [hs, exec_subi (show Reg.r3 ≠ .r0 by decide) (show 3 ≤ 2 ^ 15 by decide)]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hb]

theorem low_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = 2 * p.L + 2 * p.L by omega, bytesAt_add, ← List.replicate_append_replicate]
  rw [h (p.kp, 2 * p.L) (by simp [keyOutsOf]), h (p.slot 2, 2 * p.L) (by simp [keyOutsOf])]

theorem high_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = p.L + p.L + p.L + p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L + p.L) = p.slot 8 by
      rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L) = p.slot 7 by
      rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega, slot_succ p 5,
    h (p.slot 5, p.L) (by simp [keyOutsOf]), h (p.slot 6, p.L) (by simp [keyOutsOf]),
    h (p.slot 7, p.L) (by simp [keyOutsOf]), h (p.slot 8, p.L) (by simp [keyOutsOf]),
    List.replicate_append_replicate, List.replicate_append_replicate, List.replicate_append_replicate]

theorem keyStatus_lt' (r : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus r < 4 := by
  unfold keyStatus; split <;> (try split) <;> decide

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After `q`: the key. -/
theorem classify_key [InvLaw] (hm : Mid p original final used st u) {c : Nat} {pB : List Byte}
    (ho : (rOf p original used st).outcome = .accepted c) (hpos : 0 < (rOf p original used st).used)
    (hph : st.phase = .q pB) :
    WP isa (.seq (keyRun keyCall) afterKey) u (Classified p original final used st) := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  obtain ⟨tr, hfin⟩ := hm.final
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hg := drop_lt hpos hrest
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hr0
  refine WP.seq (WP.mono (key_run hm.frame) fun v hk => ?_)
  have hkey : keyOf p u.mem = keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L) := by
    simp only [keyOf, hs4, hs5]
  have hstat := hk.status
  have hout := hk.out
  rw [hkey] at hstat hout
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have hwv : word v.mem p.stp 24 = BitVec.ofNat 64 0 := by
    refine Eq.trans (hk.mem.readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (rStk_sub p)
  unfold afterKey
  refine WP.seq (WP.mono (key_status_guard hstat (keyStatus_lt' _)) fun w ⟨⟨⟨he1, hax, hmem1⟩, k1⟩, hy1⟩ => ?_)
  have hgw := hk.frame.keepK k1 hmem1 hy1 (fun r hr => by revert r; decide)
  have hfin' : ∀ {r : KeySearchResult}, keySearch p.L p.eB st ((genRand original).drop used) = r →
      final = r.consume used tr := fun h => by rw [hfin, tailOf, h]
  have hfin0 := hm.final
  cases hkf : keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) with
  | inl res =>
    cases res with
    | ok key =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .ok key) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hout
      refine WP.ite true he1 (fun _ => ?_) (fun h => by cases h)
      refine WP.mono (finish_done (final := final) hgw (by decide) (by rw [hks]; rfl) (by rw [hks]; rfl)
        (by rw [hks]; rfl) hrem ?_ ⟨0, by rw [hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr ⟨?_, h⟩
      · rw [hmem1, key_outs, hout, hks]
        simp only [keySearchBytes, Spec.Entropy.Result.consume, keyBytes, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
      · rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
        · rw [ho] at h; cases h
        · rw [hph] at h'; cases h'
        · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
    | error fl =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .error fl) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hax
      refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
      refine WP.seq (WP.mono (sub_guard3_r11 hax (by decide)) fun w2 ⟨⟨⟨he2, hmem2⟩, k2⟩, hy2⟩ => ?_)
      have hgw2 := hgw.keepK k2 hmem2 hy2 (fun r hr => by revert r; decide)
      refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
      refine WP.mono (fail_done (final := final) hgw2 (by decide) (by rw [hks]; rfl) (by rw [hks]; rfl)
        (by rw [hks]; rfl) hrem (by rw [hks]; rfl)
        ⟨0, by rw [hmem2, hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
      · rw [ho] at h; cases h
      · rw [hph] at h'; cases h'
      · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
  | inr _ =>
    have hks := ks_accepted_small (L := p.L) (eB := p.eB) ho hg hph hkf
    simp only [keyOp, hkf, keyStatus] at he1 hax hout
    refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (sub_guard3_r11 hax (by decide)) fun w2 ⟨⟨⟨he2, hmem2⟩, k2⟩, hy2⟩ => ?_)
    have hgw2 := hgw.keepK k2 hmem2 hy2 (fun r hr => by revert r; decide)
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (nextPrime_ok hgw2 (phase := 0) (by decide)) fun t ⟨⟨htm, k3⟩, hy3⟩ =>
      Or.inl ⟨.inr ⟨c, ho, by omega, .inr ⟨pB, hph, hkf⟩⟩, ?_⟩
    have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]
        [(10, BitVec.ofNat 64 4)] := by
      constructor
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
    obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left, .p, limitOf p.L p.eB⟩) hgw2 hv htm k3.rd k3.wr k3.sp hy3
      (fun r hr => k3.gpr r (by revert r hr; decide)) rfl rfl hgw2.state.left (Nat.le_refl _) hgw2.state.left_lt
      (by rw [hmem2, hmem1]; exact low_of_outs hout) (by rw [hmem2, hmem1]; exact high_of_outs hout)
      (fun _ h => by cases h) (by rw [hmem2, hmem1]; exact hwv)
    refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st) ++ [1, 2], hlive, measure_lt p hpos hle (Nat.le_refl _),
      ?_, rfl, .inr (.inr ⟨c, pB, ho, hph, rfl, rfl, rfl⟩)⟩, hfin0⟩
    rw [tailOf, hks, tailOf, List.drop_drop]

end

/-! ## The loop -/

section

variable {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After the search: what it leaves, classified. -/
theorem classify_ok [InvLaw] (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (classify keyCall) t (Classified p original final used st) := by
  have hf := hi.1.input.cfacts
  unfold classify
  simp only [seqs]
  refine WP.seq (WP.mono (after_head hi ha) fun u ⟨hax, hcx, hm⟩ => ?_)
  have hu64 : (rOf p original used st).used < 2 ^ 64 := by
    have := hm.frame.used_le; have := hf.rand64; omega
  have he := eval_zero_ofNat u .r3 (by have := prime_status_lt (rOf p original used st); omega) hax
  cases ho : (rOf p original used st).outcome with
  | entropy k a =>
    have hs : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
    rw [hs] at he
    exact WP.ite true he (fun _ => classify_entropy hm hax ho) (fun h => by cases h)
  | exhausted =>
    have hs : (rOf p original used st).status = 3 := by rw [rOf_status, ho]; rfl
    rw [hs] at he hax
    refine WP.ite false he (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (sub_guard3_r12 hax (by decide)) fun v ⟨⟨⟨he2, hmem⟩, k⟩, hy⟩ => ?_)
    have hv := hm.keepK k hmem hy (fun r hr => by revert r; decide)
    exact WP.ite true he2 (fun _ => classify_exhausted hv ho) (fun h => by cases h)
  | accepted c =>
    have hs : (rOf p original used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs] at he hax
    refine WP.ite false he (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (sub_guard3_r12 hax (by decide)) fun v ⟨⟨⟨he2, hmem⟩, k⟩, hy⟩ => ?_)
    have hv := hm.keepK k hmem hy (fun r hr => by revert r; decide)
    have hcx' : v.gpr .r11 = BitVec.ofNat 64 (rOf p original used st).used := by
      rw [k.gpr .r11 (by decide)]; exact hcx
    refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
    have he3 := eval_zero_ofNat v .r11 hu64 hcx'
    refine WP.ite (decide ((rOf p original used st).used = 0)) he3 (fun h0 => ?_) (fun h0 => ?_)
    · refine WP.mono (classify_none hv ho (of_decide_eq_true h0)) fun _ h => Or.inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', -, hu, -⟩)
      · rw [ho] at h; cases h
      · exact hu (of_decide_eq_true h0)
    · have hpos : 0 < (rOf p original used st).used := by
        have := of_decide_eq_false h0; omega
      unfold accepted
      refine WP.seq (WP.mono (phase_ok hv.frame) fun x ⟨⟨⟨he4, _, hmem4⟩, k4⟩, hy4⟩ => ?_)
      have hx := hv.keepK k4 hmem4 hy4 (fun r hr => by revert r; decide)
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p =>
        refine WP.ite true he4 (fun _ => ?_) (fun h => by cases h)
        refine WP.mono (nextPrime_ok hx.frame (phase := 1) (by decide)) fun y ⟨⟨hym, k5⟩, hy5⟩ =>
          Or.inl ⟨.inr ⟨c, ho, by omega, .inl rfl⟩, ?_⟩
        exact classify_p hx ho hpos rfl hym k5.rd k5.wr k5.sp hy5 (fun r hr => k5.gpr r (by revert r hr; decide))
      | q pB =>
        refine WP.ite false he4 (fun h => by cases h) (fun _ => ?_)
        exact classify_key hx ho hpos rfl

/-- The loop's test: the status, against 4. -/
theorem status_guard (h : GenFrame p original used st s) {w : Nat} (hw : word s.mem p.F 80 = BitVec.ofNat 64 w)
    (h64 : w < 2 ^ 64) :
    WP isa (.block [ldf .r9 10, .subi .r9 .r9 4]) s fun t =>
      ((isa.eval (.zero .d .r9) t = some (decide (w = 4)) ∧ t.mem = s.mem) ∧ Keep [.r9] s t) ∧
        t.syms = s.syms := by
  have hw' : s.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 w := hw
  have hb := sub_ofNat_beq (n := w) (c := 4) h64 (by decide)
  refine WP.keepS [.r9] ?_ (by decide)
  prun [ldf, h.r31, h.frame_ld 80 (by decide), hw', exec_subi (show Reg.r9 ≠ .r0 by decide) (show 4 ≤ 2 ^ 15 by decide)]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, hb]

theorem GenInv.keepK {n : Nat} (h : GenInv p original final n s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hy : t.syms = s.syms) (hrs : ∀ r ∈ preserved, r ∉ rs) : GenInv p original final n t := by
  obtain ⟨used, st, hn, ⟨hl, hfin⟩⟩ := h
  refine ⟨used, st, hn, ⟨⟨hl.toGenFrame.keepK k hm hy hrs, ?_⟩, hfin⟩⟩
  rw [hm]; exact hl.key

theorem GenDone.keepK (h : GenDone p original final s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hy : t.syms = s.syms) (hrs : ∀ r ∈ preserved, r ∉ rs) : GenDone p original final t := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨g.keepK k hm hy hrs, ?_, ?_, ?_⟩ <;> rw [hm]
  exacts [h1, h2, h3]

theorem keyStatus_lt (r : KeySearchResult) : r.keyStatus < 4 := by
  unfold KeySearchResult.keyStatus
  split <;> decide

end

/-- An iteration: the search, its classification and the loop's test. -/
theorem gen_iteration [InvLaw] (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult}
    {n : Nat} (h : GenInv p original final n s) :
    WP isa (iteration (searchCall v) keyCall) s fun t =>
      (isa.eval (.zero .d .r9) t = some false ∧ GenDone p original final t) ∨
      (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, GenInv p original final m t) := by
  obtain ⟨used, st, rfl, hi⟩ := h
  unfold iteration
  simp only [seqs]
  refine WP.seq (WP.mono (search_run v hi.1) fun t ha => ?_)
  refine WP.seq (WP.mono (classify_ok hi ha) fun u hc => ?_)
  rcases hc with ⟨-, h4, -, ⟨st', e, hl', hm, htail, -, -⟩, ⟨tr, hfin⟩⟩ | ⟨-, hd⟩
  · refine WP.mono (status_guard hl'.toGenFrame h4 (by decide)) fun x ⟨⟨⟨hx, hmem⟩, k⟩, hy⟩ =>
      Or.inr ⟨hx, _, hm, ?_⟩
    refine GenInv.keepK ⟨_, st', rfl, ⟨hl', tr ++ e, ?_⟩⟩ k hmem hy (fun r hr => by revert r; decide)
    rw [hfin, htail, consume_consume]
  · have hlt := keyStatus_lt final
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega)) fun x ⟨⟨⟨hx, hmem⟩, k⟩, hy⟩ => Or.inl ⟨?_, ?_⟩
    · refine hx.trans ?_; congr 1; simp only [decide_eq_false_iff_not]; omega
    · exact hd.keepK k hmem hy (fun r hr => by revert r; decide)

theorem gen_loop [InvLaw] (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult} {n : Nat}
    (h : GenInv p original final n s) :
    WP isa (.loop (iteration (searchCall v) keyCall) (.zero .d .r9)) s (GenDone p original final) :=
  WP.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .zero .d .r9) (Q := GenDone p original final)
    (GenInv p original final) (fun _ _ h => gen_iteration v h) n s h

end VG.Proof.RsaKeyGen.PPC64LE.Generate
