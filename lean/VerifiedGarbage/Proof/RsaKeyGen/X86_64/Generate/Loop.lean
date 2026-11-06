module

public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Classify
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! # The controller's key and loop

The key's arguments, call and run, how a step ends after a prime's search or
the key, and the loop.
-/

@[expose] public section

/-! ## The key's arguments

`n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` at the key's buffer's slots 0, 2,
4, 5, 6, 7 and 8; the exponent the state's last word; the working space. The
twelve stack arguments in the call's frame of 96 octets below the
controller's.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The key's stack arguments. -/
def keyValues (p : GenPublic) : List (Nat × BitVec 64) :=
  [(0, p.slot 5), (1, BitVec.ofNat 64 p.L), (2, p.slot 6), (3, BitVec.ofNat 64 p.L), (4, p.slot 7),
    (5, BitVec.ofNat 64 p.L), (6, p.slot 8), (7, BitVec.ofNat 64 p.L), (8, p.stp + BitVec.ofNat 64 48),
    (9, BitVec.ofNat 64 8), (10, p.B), (11, BitVec.ofNat 64 (p.Z / 8))]

theorem keyValues_bound (p : GenPublic) : ∀ e ∈ keyValues p, 8 * e.1 + 8 ≤ 96 := by
  simp only [keyValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem keyValues_bound20 (p : GenPublic) : ∀ e ∈ keyValues p, e.1 < 20 := fun e he => by
  have := keyValues_bound p e he; omega

/-- The key's arguments in registers. -/
def KeyRegs (p : GenPublic) (s : State) : Prop :=
  s.gpr .rdi = p.kp ∧ s.gpr .rsi = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .rdx = p.slot 2 ∧
    s.gpr .rcx = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .r8 = p.slot 4 ∧ s.gpr .r9 = BitVec.ofNat 64 p.L

/-- A read of the frame sees past a store to the key call's frame below it. -/
theorem read_past_key (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 96)
    (he : e + 104 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 96 + BitVec.ofNat 64 d) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have hF : F + BitVec.ofNat 64 e = F - BitVec.ofNat 64 96 + BitVec.ofNat 64 (96 + e) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [hF]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := 96 + e) (n := 8) (e := d) (k := 8) (Or.inr (by omega))
    (by omega) (by omega)) (by decide)

theorem read_past_key0 (m : Mem) (F : Addr) (v : BitVec 64) {e : Nat} (he : e + 104 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 96) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have := read_past_key m F v (d := 0) (by decide) he
  rwa [BitVec.add_zero] at this

theorem key_args_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block keyArgs) (allocated 96 s) fun t =>
      KeyRegs p t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (allocated 96 s) t := by
  have scrF := h.scr
  have hl : ∀ d, d + 8 ≤ 160 →
      InRegions ((allocated 96 s).rd ++ (allocated 96 s).wr) (p.F + BitVec.ofNat 64 d) 8 := by
    intro d hd
    obtain ⟨r, hr, hc⟩ := scrF.st hd
    exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), hc⟩
  have hl0 : InRegions ((allocated 96 s).rd ++ (allocated 96 s).wr) p.F 8 := by
    simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hsp : (allocated 96 s).gpr .rsp = p.F - BitVec.ofNat 64 96 := by rw [allocated_rsp, h.rsp]
  have hr12 : (allocated 96 s).gpr .r12 = p.F := by rw [allocated_reg _ _ _ (by decide), h.r12]
  have hF := h.input.F_toNat
  have hroom : 552 ≤ p.sp.toNat := h.input.room
  have haw : (allocated 96 s).wr = ⟨p.F - BitVec.ofNat 64 96, 96⟩ :: s.wr := by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 96, 96⟩ : Region) :: s.wr = _
    rw [h.rsp]
  have scr : Scr (allocated 96 s) (p.F - BitVec.ofNat 64 96) 96 :=
    Scr.of_mem (by rw [haw]; exact List.mem_cons_self ..) (by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 96).toNat = 96 from rfl]; omega)]
      have := h.input.top
      simp only [show (BitVec.ofNat 64 96).toNat = 96 from rfl]
      omega)
  have hs : ∀ d, d + 8 ≤ 96 → InRegions (allocated 96 s).wr (p.F - BitVec.ofNat 64 96 + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 96 s).wr (p.F - BitVec.ofNat 64 96) 8 := by
    simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hv0 := h.header (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv5 := h.header (j := 5) (v := p.B) (by simp [GenPublic.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1 hv5 hv6 hv7
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have h2 : BitVec.ofNat 64 p.L <<< 1 = BitVec.ofNat 64 (2 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h24 : p.kp + BitVec.ofNat 64 (2 * p.L) + BitVec.ofNat 64 (2 * p.L) = p.slot 4 := by
    rw [GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  have hn (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; rw [Nat.succ_mul]
  have h45 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := hn 4
  have h56 : p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 := hn 5
  have h67 : p.slot 6 + BitVec.ofNat 64 p.L = p.slot 7 := hn 6
  have h78 : p.slot 7 + BitVec.ofNat 64 p.L = p.slot 8 := hn 7
  have h8 : (8 : BitVec 32).setWidth 64 = BitVec.ofNat 64 8 := by decide
  have h48 : BitVec.signExtend 64 (48 : BitVec 32) = BitVec.ofNat 64 48 := by decide
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t =>
    KeyRegs p t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold keyArgs KeyRegs writeFrame keyValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, allocated_mem,
    hsp, hr12, hl0, hl 8 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    read_past_key, read_past_key0, hv0, hv1, hv5, hv6, hv7, h2, h24, h45, h56, h67, h78, h8, h48,
    hs0, hs 8 (by decide), hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide),
    hs 48 (by decide), hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide),
    hs 88 (by decide)]

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The key's call

Its regions: the key's buffer's slots, the exponent in the state, the
working space, its stack arguments and its return address; its
precondition at its entry, from the controller's.
-/

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

/-! ## The key, run

`keyRun`: in a frame of its stack arguments, the key's arguments and its
call. It leaves the key's status and its outputs at the key's buffer, and
writes nothing else but the working space and the stack.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem freed freed_rsp
  freed_reg freed_mem frame_alloc)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The key, as the controller calls it. -/
def keyCall : Prog isa := .call "vg_rsa_keygen_key" VG.Impl.RsaKeyGen.X86_64.Key.code

theorem keyCode_mx : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem keyCode_noSp : NoSp VG.Impl.RsaKeyGen.X86_64.Key.code := by
  have h : VG.Impl.RsaKeyGen.X86_64.Key.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    decide +kernel
  intro i hi
  rw [Code.allInstrs_eq] at h
  simpa using List.all_eq_true.mp h i hi

theorem keyCode_depth : Code.depth VG.Impl.RsaKeyGen.X86_64.Key.code = 0 := by decide +kernel

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
  status : ((t.gpr .rax).setWidth 32).toNat = keyStatus (keyOf p s.mem)
  out : match keyOf p s.mem with
    | .inl (.ok ys) => (keyOutsOf p).map (fun o => Spec.Rsa.bytesAt t.mem o.1 o.2) = ys
    | _ => ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0
  mem : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩] s.mem t.mem

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem key_covers_writes (h : GenFrame p original used st s) {u : State}
    (hw : u.wr = (allocated 96 s).wr) : Covers (kWrites p) u.wr := by
  have hf := h.input.cfacts
  have hk := h.key_region
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  rw [hk, hs] at hwo
  rw [hw]
  have hin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), rS p], q ∈ (allocated 96 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  obtain ⟨hL1, -, -⟩ := hf.len
  refine Covers.of_sub fun r hr => ?_
  simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 0, by simp, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 2 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 4 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 5 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 6 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 7 * p.L, rfl, by simp; omega⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), 8 * p.L, rfl, by simp; omega⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩

theorem key_covers_reads (h : GenFrame p original used st s) {u : State}
    (hrd : u.rd = (allocated 96 s).rd) (hw : u.wr = (allocated 96 s).wr) :
    Covers (kReads p ++ kWrites p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (key_covers_writes h hw).right
  have ht : inState original = cS p := by rw [← h.input.2]; rfl
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  rw [ht] at hwo
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [kReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · refine ⟨cS p, List.mem_append_right _ ?_, 48, rfl, by simp⟩
    show cS p ∈ _ :: s.wr
    rw [h.wr, hwo]; simp
  · refine ⟨⟨s.gpr .rsp - BitVec.ofNat 64 96, 96⟩, List.mem_append_right _ (List.mem_cons_self ..), 0, ?_, by simp⟩
    rw [h.rsp, F_96, BitVec.add_zero]

theorem key_frame_sub (h : GenFrame p original used st s) :
    ∀ r ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)],
      ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hk := h.key_region
  have hs : inScr original = rS p := by rw [← h.input.2]; rfl
  have hS : (⟨original.gpr .rsp - BitVec.ofNat 64 stackUse, 392⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 552, 392⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hs, hS]
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end

/-- The key's result at its entry: the key from the slots of `p` and `q`. -/
theorem callK_res {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256) (ha : KeyRegs p u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) :
    Key.keyRes (callK p u) = keyOf p s.mem ∧
      Spec.Rsa.bytesAt (callK p u).mem (Key.arg (callK p u) 8) (Key.arg (callK p u) 9).toNat = p.eB := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := callK_args (s := s) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hcf := callK_frame (s := s) hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -⟩ := hst
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callK p u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hcf.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR]
  have he : Spec.Rsa.bytesAt (callK p u).mem (Key.arg (callK p u) 8) (Key.arg (callK p u) 9).toNat = p.eB := by
    rw [show Key.arg (callK p u) 8 = _ from a8, show Key.arg (callK p u) 9 = _ from a9,
      toNat_ofNat_lt (show 8 < 2 ^ 64 by decide),
      hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide)]
    exact h.state.e
  refine ⟨?_, he⟩
  simp only [Key.keyRes, Key.arg, callK_gpr (show Reg.r8 ≠ .rsp by decide),
    callK_gpr (show Reg.r9 ≠ .rsp by decide), h8, h9, tl]
  rw [show stackArg (callK p u) 0 = _ from a0]
  rw [show Spec.Rsa.bytesAt (callK p u).mem (stackArg (callK p u) 8) (stackArg (callK p u) 9).toNat = p.eB from he,
    hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega),
    hbytes (R := ⟨p.slot 5, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega)]

theorem key_run [Key.KeyProof] {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (keyRun keyCall) s (AfterKey p original used st s) := by
  have hf := h.input.cfacts
  have hF := h.input.F_toNat
  have hroom := h.input.room
  unfold keyRun keyCall
  apply frame_alloc (by decide) (by decide) (by decide) (by rw [h.rsp, hF]; have : 552 ≤ p.sp.toNat := hroom; omega)
  refine WP.seq (WP.mono (key_args_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 256 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp, F_96]
  refine WP.call_mx (k := Key.keyCtr) (Key.KeyProof.correct keyCode_mx) keyCode_noSp
    (by rw [keyCode_depth]; decide) (callK_pre h hu ha hm) (key_covers_reads h k.2.1 k.2.2)
    (key_covers_writes h k.2.2) fun t htr htw hg hfr _ ⟨s₂, hm₂, hg₂, hpost⟩ _ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := callK_args (s := s) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  obtain ⟨hL1, hL2, hL3⟩ := hf.len
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have t2 : (BitVec.ofNat 64 (2 * p.L)).toNat = 2 * p.L := toNat_ofNat_lt (by omega)
  have hcf := callK_frame (s := s) hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -⟩ := hst
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callK p u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hcf.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR]
  have hres : Key.keyRes (callK p u) = keyOf p s.mem := by
    simp only [Key.keyRes, Key.arg, callK_gpr (show Reg.r8 ≠ .rsp by decide),
      callK_gpr (show Reg.r9 ≠ .rsp by decide), h8, h9, tl]
    rw [show stackArg (callK p u) 8 = _ from a8, show stackArg (callK p u) 9 = _ from a9,
      show stackArg (callK p u) 0 = _ from a0, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide),
      hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega),
      hbytes (R := ⟨p.slot 5, p.L⟩) (.inl (kSlot_sub (by omega))) (by show p.L ≤ 2 ^ 64; omega)]
    have he : Spec.Rsa.bytesAt s.mem (p.stp + BitVec.ofNat 64 48) 8 = p.eB := h.state.e
    rw [he]
  have houts : Key.keyOuts (callK p u) = keyOutsOf p := by
    simp only [Key.keyOuts, Key.arg, callK_gpr (show Reg.rdi ≠ .rsp by decide),
      callK_gpr (show Reg.rsi ≠ .rsp by decide), callK_gpr (show Reg.rdx ≠ .rsp by decide),
      callK_gpr (show Reg.r8 ≠ .rsp by decide), callK_gpr (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, h8,
      h9, tl, t2]
    rw [show stackArg (callK p u) 0 = _ from a0, show stackArg (callK p u) 2 = _ from a2,
      show stackArg (callK p u) 4 = _ from a4, show stackArg (callK p u) 6 = _ from a6]
    rfl
  obtain ⟨hstat, hout⟩ := hpost
  rw [hres] at hstat hout
  rw [houts] at hout
  -- The memory: the stack arguments, then the key.
  have mK : cK p ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)] := List.mem_cons_self ..
  have mS : rS p ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)] :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have mT : (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region) ∈ [cK p, rS p, (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region)] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f₀ : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩] s.mem u.mem := by
    rw [hm, F_96]
    apply (Search.writeFrame_frame_size _ _ (keyValues p) (size := 96) (by decide) (keyValues_bound p)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, mT, Offset.sub_below _ (by decide) (by decide)⟩
  have hbelow : Region.Sub (below (p.sp - BitVec.ofNat 64 256) 8) ⟨p.sp - BitVec.ofNat 64 552, 392⟩ := by
    simp only [below, BitVec.sub_sub]
    rw [← BitVec.ofNat_add]
    exact Offset.sub_below _ (by decide) (by decide)
  have f₁ : Frame [cK p, rS p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩] u.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [kWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cK p, mK, kN_sub⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨cK p, mK, kSlot_sub (by omega)⟩
      · exact ⟨rS p, mS, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, mT, ?_⟩
      rw [hu, keyCode_depth]
      exact hbelow
  have hframe := f₀.trans f₁
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d := by
    refine hframe.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega)) (fun q hq => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hf.kT.symm
    · exact hf.sT.symm
    · exact sT.sub_right (Region.sub_prefix (by decide))
  have htsp : t.gpr .rsp = (allocated 96 s).gpr .rsp := by rw [hg _ (by decide), k.gpr (by decide)]
  refine ⟨htsp, htw.trans k.2.2, h.restore (htr.trans k.2.1) (show t.wr.tail = s.wr by rw [htw, k.2.2]; rfl)
      (fun r hr => ?_) (hframe.sub (key_frame_sub h)) ((hword 0 (by decide)).trans h.state.remaining)
      ((hword 8 (by decide)).trans h.state.len) ((hword 16 (by decide)).trans h.state.cap) (.inl rfl) rfl
      h.state.remaining_le, ?_, ?_, hframe⟩
  · have hnot : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by revert r; decide
    by_cases he : r = .rsp
    · subst he
      rw [freed_rsp, htsp, allocated_rsp]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ he, hg r hr, k.gpr hnot, allocated_reg _ _ _ he]
  · rw [freed_reg _ _ _ (by decide), ← hg₂ _ (by decide)]; exact hstat
  · rw [freed_mem, ← hm₂]; exact hout

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## After a prime's search

The loop's states: one about to search (`GenIter`, from `Data.lean`), with a
measure that each step that goes on lowers (`genMeasure`), and one that ended
the key search with `final` (`GenDone`). After a search and the count of the
octets it consumed (`Mid`): the frame for the octets consumed so far and the
search's counted candidates left, the search's status and consumption in
registers, and the key's buffer.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

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
  simp only [Function.comp, Offset.add_add]

/-- The key's buffer: the low four slots, `p`'s, `q`'s and the high three. -/
theorem key_bytes (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) = Spec.Rsa.bytesAt m p.kp (4 * p.L) ++
      Spec.Rsa.bytesAt m (p.slot 4) p.L ++ Spec.Rsa.bytesAt m (p.slot 5) p.L ++
      Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) := by
  rw [show 9 * p.L = 4 * p.L + p.L + p.L + 3 * p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]

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
  · exact (sK.sub_left hR).sub_right
      (show Region.Sub (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region) (cStack p) from Region.sub_prefix (by decide))

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
  exact bytes_kept (writeFrame_frame _ _ _ fun e he => by
    obtain rfl := List.mem_singleton.mp he; show 8 < 20; decide) (h.frame_key.sub_right hR) hn

theorem slot_disj (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.slot i, a⟩ : Region).Disjoint ⟨p.slot j, b⟩ := kk hf h ha hb

theorem low_disj (hf : CFacts p) {j b : Nat} (h : 4 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.kp, 4 * p.L⟩ : Region).Disjoint ⟨p.slot j, b⟩ := by
  have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

end

/-- The status and the count of the octets consumed, after the search. -/
theorem after_head {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (.block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)), .mov .rcx (.mem { base := .rcx }),
      .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx), .store (field 8) .rdx,
      .alu .test .rax (.reg .rax)]) t fun u =>
      eval .e u = some (decide ((rOf p original used st).status = 0)) ∧
        u.gpr .rax = BitVec.ofNat 64 (rOf p original used st).status ∧
        u.gpr .rcx = BitVec.ofNat 64 (rOf p original used st).used ∧ Mid p original final used st u := by
  obtain ⟨hl, hfin⟩ := hi
  have hf := hl.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := rOf_used_le hl.toGenFrame
  refine WP.mono (head_ok ha.frame ha.status ha.usedw) fun u ⟨⟨he, hax, hcx, hm⟩, k⟩ => ⟨he, hax, hcx, ?_⟩
  rw [SearchInit.add_ofNat] at hm
  have hb : ∀ e ∈ [(8, BitVec.ofNat 64 (used + (rOf p original used st).used))], e.1 < 20 := by
    intro e he; obtain rfl := List.mem_singleton.mp he; show 8 < 20; decide
  have hhead : ∀ {R : Region}, Region.Sub R (cK p) → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt t.mem R.base R.len :=
    fun hR hn => head_kept ha.frame hm hR hn
  have hkey := hl.key
  have hph := phaseWord_le st.phase
  -- The key's buffer after the search.
  have hlow : Spec.Rsa.bytesAt t.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [← hkey.low]
    refine search_kept hl ha.mem (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) ?_ (by
      show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact low_disj hf (by decide) (by omega)
    · exact low_disj hf (by decide) (by omega)
  have hsplit : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) =
      Spec.Rsa.bytesAt s.mem (p.slot 5) p.L ++ Spec.Rsa.bytesAt s.mem (p.slot 6) (3 * p.L) := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega]
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
  refine ⟨ha.frame.store hle _ hb (by intro e he; obtain rfl := List.mem_singleton.mp he; show 9 ≠ 8; decide) hm k.2.1 k.2.2
      (fun r hr => k.gpr (by revert r; decide)) (by rw [hm]; exact slots_used ha.frame _ [] (by simp) (by simp)),
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
    refine Eq.trans ((writeFrame_frame _ _ _ hb).readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hreq
    obtain rfl := List.mem_singleton.mp hq
    exact ha.frame.state_frame.symm

/-- A frame through a step that changes no memory and keeps the regions and
the callee-saved registers. -/
theorem GenFrame.keep {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : GenFrame p original used st t := by
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, (hg .rsp (by decide)).trans h.rsp,
    (hg .r12 (by decide)).trans h.r12, fun reg hreg hne hs => (hg reg hreg).trans (h.saved reg hreg hne hs),
    ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedR12, h.random, h.headers, h.state]

theorem Mid.keep {p : GenPublic} {original u v : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (h : Mid p original final used st u) (hm : v.mem = u.mem) (hr : v.rd = u.rd)
    (hw : v.wr = u.wr) (hg : ∀ r ∈ calleeSaved, v.gpr r = u.gpr r) : Mid p original final used st v := by
  refine ⟨h.frame.keep hm hr hw hg, h.final, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.low, h.slot4, h.slot5, h.high, h.req]

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## How a step ends

Zeros at the whole key's buffer (`clearAll`); the end of the key search
(`finishWith`), to `GenDone`; and the start of the next prime's search,
to a loop state of a lower measure.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem setAll_ok (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
      .mov .rdx (.reg .rcx), .shift .shl .rcx 3, .alu .add .rcx (.reg .rdx), .store (field 13) .rcx]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L)] ∧
        Keep [.rax, .rcx, .rdx] s t := by
  have scr := h.scr
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 8) 8 := scr.ld (d := 8) (by decide)
  have hs12 : InRegions s.wr (p.F + BitVec.ofNat 64 96) 8 := scr.st (d := 96) (by decide)
  have hs13 : InRegions s.wr (p.F + BitVec.ofNat 64 104) 8 := scr.st (d := 104) (by decide)
  have h0 := h.header (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have h1 := h.header (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keep [.rax, .rcx, .rdx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl8, read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs12, hs13]

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
  refine WP.seq (WP.mono (setAll_ok h) fun t1 ⟨hm1, k1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 (by decide)
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
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hnst : p.stp.toNat + 56 ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inState original) (by simp [inWrites])
    rwa [h.state_region] at this
  rw [← writeFrame_word _ _ _ hsb j (by omega)]
  exact (writeFrame_frame _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
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

/-- `finishWith status`: the key search ended with `final`. -/
theorem finish_done {p : GenPublic} {original s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p original u st s) {status : Nat} (hstat : status < 4)
    (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩) (hs : final.keyStatus = status)
    (hr0 : st.remaining = 0)
    (hkey : Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (.block (finishWith status)) s (GenDone p original final) := by
  refine WP.mono (finishWith_ok h hstat) fun t ⟨hm, k⟩ => ?_
  have hv : StateStores [(4, (0 : BitVec 64)), (5, (0 : BitVec 64))] [(10, BitVec.ofNat 64 status)] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have h0 := h.state.remaining
  rw [hr0] at h0
  have hg : GenFrame p original u ⟨0, .p, 0⟩ t :=
    h.setState hv hm k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide)) h0 rfl rfl (Nat.zero_le _) (by decide)
  obtain ⟨req, hw, hr⟩ := hreq
  refine ⟨by rw [hu, hpr]; exact hg, ?_, ?_, ⟨req, ?_, hr⟩⟩
  · rw [hm, writeFrame_word _ _ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; show 10 < 20; decide) 10 (by decide), hs]
    rfl
  · rw [hm]
    have := stores_key h hv (j := 0) (n := 9 * p.L) (by omega)
    rw [Nat.zero_mul, ← kp_zero] at this
    rw [this, hkey]
  · rw [hm]
    exact (stores_word h hv 3 (by decide)).trans hw

/-- The start of the next prime's search, for the progress `st'`: a loop
state, its status 4. -/
theorem cont_of {p : GenPublic} {original s t : State} {u : Nat} {st st' : KeyProgress}
    (h : GenFrame p original u st s) {sv : List (Nat × BitVec 64)}
    (hv : StateStores sv [(10, (4 : BitVec 64))])
    (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F [(10, (4 : BitVec 64))])
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
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
  have hg' := h.setState hv hm hr hw hg h0 h4 h5 hrem hlt
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

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## A prime's search that asked for entropy or was exhausted

After the search and the count of its octets (`Mid`): the key search asks for
more entropy with the search's state; or the generation fails, and the key
search is exhausted or starts the next generation.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

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

/-- Whether the key search goes on after the prime's search from `st`: to the
next generation, to `q` after `p`, or to both primes again after a `d` too
small. -/
def ContSpec (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : Prop :=
  ((rOf p original used st).outcome = .exhausted ∧ ¬st.left < 2) ∨
  (∃ c, (rOf p original used st).outcome = .accepted c ∧ (rOf p original used st).used ≠ 0 ∧
    (st.phase = .p ∨ ∃ pB, st.phase = .q pB ∧ keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) = .inr ()))

/-- After a step: the next prime's search, or the key search ended with
`final`. -/
def Classified (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  (ContSpec p original used st ∧ Cont p original final used st t) ∨
    (¬ContSpec p original used st ∧ GenDone p original final t)

theorem test_guard {s : State} {n : Nat} (hs : s.gpr .rcx = BitVec.ofNat 64 n) (h64 : n < 2 ^ 64) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      (eval .e t = some (decide (n = 0)) ∧ t.mem = s.mem) ∧ Keep [.rcx] s t := by
  have he : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == (0 : BitVec 64)) = decide (n = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.and_self, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rcx] ?_ rfl
  xrun [hs, eval, he]

/-- The key's buffer through stores to the state and the frame. -/
theorem stores_key9 {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame s.mem p.stp sv) p.F fv) p.kp (9 * p.L) =
      Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) := by
  have := stores_key h hv (j := 0) (n := 9 * p.L) (by omega)
  rwa [Nat.zero_mul, ← kp_zero] at this

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

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem rOf_status (r : PrimeSearchResult) : r.status = r.outcome.status := rfl

/-- The search asked for more entropy: so does the key search. -/
theorem classify_entropy (hm : Mid p original final used st u)
    (hax : u.gpr .rax = BitVec.ofNat 64 (rOf p original used st).status) {k a : Nat}
    (ho : (rOf p original used st).outcome = .entropy k a) :
    WP isa (.block [.store (field 10) .rax]) u (Classified p original final used st) := by
  have hf := hm.frame.input.cfacts
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
  refine WP.mono (storeStatus_ok hframe hax) fun t ⟨htm, k'⟩ => Or.inr ⟨?_, ?_⟩
  · rintro (⟨h, -⟩ | ⟨c, h, -⟩) <;> rw [ho] at h <;> cases h
  have hv : StateStores [] [(10, BitVec.ofNat 64 0)] := by
    constructor
    · simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hg : GenFrame p original (used + (rOf p original used st).used) ⟨st.left, st.phase, k⟩ t :=
    hframe.setState hv htm k'.2.1 k'.2.2 (fun r _ => k'.gpr (by simp)) hframe.state.remaining
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
    (hl : st.left < 2) :
    WP isa (fail 3) u (GenDone p original final) := by
  have hrem : (rOf p original used st).remaining = 0 := by
    simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_last (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p original used st).used,
      tr ++ primeEntry (rOf p original used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done hm.frame (by decide) rfl rfl rfl hrem rfl ⟨req, hw, by rw [hr0]; rfl⟩

/-- The search was exhausted: the next generation, from `p`. -/
theorem classify_next (hm : Mid p original final used st u) (ho : (rOf p original used st).outcome = .exhausted)
    (hl : ¬st.left < 2) {t : State}
    (htm : t.mem = writeFrame (writeFrame u.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
      (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, (4 : BitVec 64))])
    (hr : t.rd = u.rd) (hw : t.wr = u.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = u.gpr r) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hks := ks_exhausted_next (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (by omega)
  have hv : StateStores [(5, BitVec.ofNat 64 (st.left - 1)), (0, BitVec.ofNat 64 (limitOf p.L p.eB)),
      (4, BitVec.ofNat 64 0)] [(10, (4 : BitVec 64))] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hout : outBytes p.L (rOf p original used st) = List.replicate p.L 0 := by
    simp only [outBytes, ho]
  have hlt := hm.frame.state.left_lt
  have hle := hm.frame.used_le
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, hm.slot5, hm.high,
      ← List.replicate_append_replicate]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => rfl
    | q pB => simp only [hout]
  have hreq0 : word u.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [hw', this]
  obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left - 1, .p, limitOf p.L p.eB⟩) hm.frame hv htm hr hw hg rfl
    rfl rfl (Nat.le_refl _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hm.frame.state.left_lt) hm.low hhigh5
    (fun _ h => by cases h) hreq0
  refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st), hlive, ?_, ?_, rfl, .inl ⟨ho, rfl, rfl, rfl⟩⟩, hm.final⟩
  · unfold genMeasure
    dsimp only
    have hmul : (p.randLen - (used + (rOf p original used st).used)) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## A generation exhausted, or a prime accepted

`exhaustedGen`: the last generation, or the next. A prime accepted: the key
search is exhausted if it read nothing; `q` next after `p`; after `q`, the
key, which ends the key search, or, for a `d` too small, both primes again.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- One generation fewer, and the next prime's search from `p`. -/
theorem dec_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hax : s.gpr .rax = p.stp)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 st.left) (hl : 2 ≤ st.left) :
    WP isa (.block (([.alu .sub .rcx (.imm 1), .store (stw 5) .rcx] : List Instr) ++ nextPrime 0)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(5, BitVec.ofNat 64 (st.left - 1)),
        (0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]) p.F [(10, (4 : BitVec 64))] ∧
        Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.header (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl11 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 88) 8 := scr.ld (d := 88) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs0 : InRegions s.wr p.stp 8 := by simpa only [off, BitVec.add_zero] using sst.st (d := 0) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  simp only [Nat.reduceMul] at h7 h11
  have hlt := h.state.left_lt
  have hsub : BitVec.ofNat 64 st.left - (1 : BitVec 64) = BitVec.ofNat 64 (st.left - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show st.left - 1 < 2 ^ 64 by omega)]
    omega
  have hnF : p.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hnS : p.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 160) :
      (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 d) 64 =
        s.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨p.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega))).readW (r := p.frame)
      (Offset.contains_base _ hd (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact h.state_frame) (by decide)
  have hk7 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 56) 64 =
      p.stp := fun v => (hkeep v 56 (by decide)).trans h7
  have hk11 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 88) 64 =
      BitVec.ofNat 64 (limitOf p.L p.eB) := fun v => (hkeep v 88 (by decide)).trans h11
  have h0 : (BitVec.ofNat 32 0).setWidth 64 = BitVec.ofNat 64 0 := by decide
  have h4 : (4 : BitVec 32).setWidth 64 = (4 : BitVec 64) := by decide
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append]
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl11, hs10, hs0, hs4, hs5, hk7, hk11, hax, hcx, hsub, h0, h4]

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- `exhaustedGen`: the key search exhausted, or the next generation. -/
theorem classify_exhausted (hm : Mid p original final used st u)
    (ho : (rOf p original used st).outcome = .exhausted) :
    WP isa exhaustedGen u (Classified p original final used st) := by
  unfold exhaustedGen
  refine WP.seq (WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hax, hcx, hmem⟩, k⟩ => ?_)
  have hv := hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
  refine WP.ite (decide (st.left < 2)) hb (fun hl => ?_) (fun hl => ?_)
  · refine WP.mono (classify_last hv ho (of_decide_eq_true hl)) fun _ h => Or.inr ⟨?_, h⟩
    rintro (⟨-, h⟩ | ⟨c, h, -⟩)
    · exact h (of_decide_eq_true hl)
    · rw [ho] at h; cases h
  · have hl' := of_decide_eq_false hl
    refine WP.mono (dec_ok hv.frame hax hcx (by show 2 ≤ st.left; omega)) fun t ⟨htm, k2⟩ =>
      Or.inl ⟨.inl ⟨ho, hl'⟩, ?_⟩
    exact classify_next hv ho hl' htm k2.2.1 k2.2.2 (fun r hr => k2.gpr (by revert r; decide))

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
      (4, BitVec.ofNat 64 1)]) p.F [(10, (4 : BitVec 64))])
    (hr : t.rd = u.rd) (hw : t.wr = u.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = u.gpr r) :
    Cont p original final used st t := by
  have hf := hm.frame.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := hm.frame.used_le
  have hrest : (rOf p original used st).used ≤ ((genRand original).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hks := ks_accepted_p (L := p.L) (eB := p.eB) (st := st) (rand := (genRand original).drop used) ho
    (drop_lt hpos hrest) hph
  have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 1)]
      [(10, (4 : BitVec 64))] := by
    constructor
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs4
  have hhigh5 : Spec.Rsa.bytesAt u.mem (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, hs5, hm.high,
      ← List.replicate_append_replicate]
  have hreq0 : word u.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [hw', this]
  obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left, .q (Spec.Rsa.i2osp c p.L), limitOf p.L p.eB⟩) hm.frame
    hv htm hr hw hg rfl rfl hm.frame.state.left (Nat.le_refl _) hm.frame.state.left_lt hm.low hhigh5
    (fun pB h => by cases h; exact hs4) hreq0
  refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st), hlive, measure_lt p hpos hle (Nat.le_refl _), ?_, rfl,
    .inr (.inl ⟨c, ho, hph, rfl, rfl, rfl⟩)⟩, hm.final⟩
  rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The key from `p` and `q`

After `q`'s search accepted a prime: the key, which ends the key search with
it or with its failed check, or, for a `d` too small, both primes again in
the same generation.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (candidate_status_guard second_status_guard)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem status_of {s t : State} {status : Nat}
    (hs : ((s.gpr .rax).setWidth 32).toNat = status)
    (ht : t.gpr .rax = ((s.gpr .rax).setWidth 32).setWidth 64) :
    t.gpr .rax = BitVec.ofNat 64 status := by
  apply BitVec.eq_of_toNat_eq
  rw [ht, BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]

theorem low_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = 2 * p.L + 2 * p.L by omega, bytesAt_add, ← List.replicate_append_replicate]
  rw [h (p.kp, 2 * p.L) (by simp [keyOutsOf]), h (p.slot 2, 2 * p.L) (by simp [keyOutsOf])]

theorem high_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  have e (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; rw [Nat.succ_mul]
  rw [show 4 * p.L = p.L + p.L + p.L + p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L + p.L) = p.slot 8 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L) = p.slot 7 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, e 5,
    h (p.slot 5, p.L) (by simp [keyOutsOf]), h (p.slot 6, p.L) (by simp [keyOutsOf]),
    h (p.slot 7, p.L) (by simp [keyOutsOf]), h (p.slot 8, p.L) (by simp [keyOutsOf]),
    List.replicate_append_replicate, List.replicate_append_replicate, List.replicate_append_replicate]

section

variable {p : GenPublic} {original u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After `q`: the key. -/
theorem classify_key [Key.KeyProof] (hm : Mid p original final used st u) {c : Nat} {pB : List Byte}
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
    · exact sT.sub_right (Region.sub_prefix (by decide))
  unfold afterKey
  refine WP.seq (WP.mono (candidate_status_guard v) fun w ⟨⟨he1, hax1, hmem1⟩, k1⟩ => ?_)
  have hgw := hk.frame.keep hmem1 k1.2.1 k1.2.2 (fun r hr => k1.gpr (by revert r; decide))
  have hax := status_of hstat hax1
  rw [hstat] at he1
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
      refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
      have hgw2 := hgw.keep hmem2 k2.2.1 k2.2.2 (fun r hr => k2.gpr (by revert r; decide))
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
    refine WP.seq (WP.mono (second_status_guard hax (by decide)) fun w2 ⟨⟨he2, hmem2⟩, k2⟩ => ?_)
    have hgw2 := hgw.keep hmem2 k2.2.1 k2.2.2 (fun r hr => k2.gpr (by revert r; decide))
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (nextPrime_ok hgw2 (phase := 0) (by decide)) fun t ⟨htm, k3⟩ =>
      Or.inl ⟨.inr ⟨c, ho, by omega, .inr ⟨pB, hph, hkf⟩⟩, ?_⟩
    have hv : StateStores [(0, BitVec.ofNat 64 (limitOf p.L p.eB)), (4, BitVec.ofNat 64 0)]
        [(10, (4 : BitVec 64))] := by
      constructor
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; simp
    obtain ⟨h4, hlive, hq0⟩ := cont_of (st' := ⟨st.left, .p, limitOf p.L p.eB⟩) hgw2 hv htm k3.2.1 k3.2.2
      (fun r hr => k3.gpr (by revert r; decide)) rfl rfl hgw2.state.left (Nat.le_refl _) hgw2.state.left_lt
      (by rw [hmem2, hmem1]; exact low_of_outs hout) (by rw [hmem2, hmem1]; exact high_of_outs hout)
      (fun _ h => by cases h) (by rw [hmem2, hmem1]; exact hwv)
    refine ⟨h4, hq0, ⟨_, primeEntry (rOf p original used st) ++ [1, 2], hlive, measure_lt p hpos hle (Nat.le_refl _),
      ?_, rfl, .inr (.inr ⟨c, pB, ho, hph, rfl, rfl, rfl⟩)⟩, hfin0⟩
    rw [tailOf, hks, tailOf, List.drop_drop]

end

end VG.Proof.RsaKeyGen.X86_64.Generate

/-! ## The loop

Each iteration searches for the progress' prime, classifies the result, and
goes on while the status is 4, to a state of a lower measure; the loop ends
with the key search's result.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (second_status_guard)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem cmp3_guard {s : State} {status : Nat}
    (hs : s.gpr .rax = BitVec.ofNat 64 status) (h64 : status < 2 ^ 64) :
    WP isa (.block [.alu .cmp .rax (.imm 3)]) s fun t =>
      (eval .e t = some (decide (status = 3)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have he : (BitVec.ofNat 64 status == (3 : BitVec 64)) = decide (status = 3) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [hs, eval, sub_beq_zero, he]

section

variable {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After the search: what it leaves, classified. -/
theorem classify_ok [Key.KeyProof] (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (classify keyCall) t (Classified p original final used st) := by
  have hf := hi.1.input.cfacts
  unfold classify
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (after_head hi ha) fun u ⟨he, hax, hcx, hm⟩ => ?_)
  have hu64 : (rOf p original used st).used < 2 ^ 64 := by
    have := hm.frame.used_le; have := hf.rand64; omega
  cases ho : (rOf p original used st).outcome with
  | entropy k a =>
    have hs : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
    rw [hs] at he
    exact WP.ite true he (fun _ => classify_entropy hm hax ho) (fun h => by cases h)
  | exhausted =>
    have hs : (rOf p original used st).status = 3 := by rw [rOf_status, ho]; rfl
    rw [hs] at he hax
    refine WP.ite false he (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp3_guard hax (by decide)) fun v ⟨⟨he2, hmem⟩, k⟩ => ?_)
    have hv := hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
    exact WP.ite true he2 (fun _ => classify_exhausted hv ho) (fun h => by cases h)
  | accepted c =>
    have hs : (rOf p original used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs] at he hax
    refine WP.ite false he (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp3_guard hax (by decide)) fun v ⟨⟨he2, hmem⟩, k⟩ => ?_)
    have hv := hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
    have hcx' : v.gpr .rcx = BitVec.ofNat 64 (rOf p original used st).used := by
      rw [k.gpr (by decide)]; exact hcx
    refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (test_guard hcx' hu64) fun w ⟨⟨he3, hmem3⟩, k3⟩ => ?_)
    have hw := hv.keep hmem3 k3.2.1 k3.2.2 (fun r hr => k3.gpr (by revert r; decide))
    refine WP.ite (decide ((rOf p original used st).used = 0)) he3 (fun h0 => ?_) (fun h0 => ?_)
    · refine WP.mono (classify_none hw ho (of_decide_eq_true h0)) fun _ h => Or.inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', -, hu, -⟩)
      · rw [ho] at h; cases h
      · exact hu (of_decide_eq_true h0)
    · have hpos : 0 < (rOf p original used st).used := by
        have := of_decide_eq_false h0; omega
      unfold accepted
      refine WP.seq (WP.mono (phase_ok hw.frame) fun x ⟨⟨he4, hmem4⟩, k4⟩ => ?_)
      have hx := hw.keep hmem4 k4.2.1 k4.2.2 (fun r hr => k4.gpr (by revert r; decide))
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p =>
        refine WP.ite true he4 (fun _ => ?_) (fun h => by cases h)
        refine WP.mono (nextPrime_ok hx.frame (phase := 1) (by decide)) fun y ⟨hym, k5⟩ =>
          Or.inl ⟨.inr ⟨c, ho, by omega, .inl rfl⟩, ?_⟩
        exact classify_p hx ho hpos rfl hym k5.2.1 k5.2.2 (fun r hr => k5.gpr (by revert r; decide))
      | q pB =>
        refine WP.ite false he4 (fun h => by cases h) (fun _ => ?_)
        exact classify_key hx ho hpos rfl

/-- The loop's test: the status, against 4. -/
theorem status_guard (h : GenFrame p original used st s) {w : Nat} (hw : word s.mem p.F 80 = BitVec.ofNat 64 w)
    (h64 : w < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (field 10)), .alu .cmp .rax (.imm 4)]) s fun t =>
      (eval .e t = some (decide (w = 4)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 80) 8 := h.scr.ld (d := 80) (by decide)
  have hw' : s.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 w := hw
  have he : (BitVec.ofNat 64 w == (4 : BitVec 64)) = decide (w = 4) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, h.r12, hl, hw', eval,
    sub_beq_zero, he]

theorem GenInv.keep {n : Nat} (h : GenInv p original final n s) (hm : t.mem = s.mem) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : GenInv p original final n t := by
  obtain ⟨used, st, hn, ⟨hl, hfin⟩⟩ := h
  refine ⟨used, st, hn, ⟨⟨hl.toGenFrame.keep hm hr hw hg, ?_⟩, hfin⟩⟩
  rw [hm]; exact hl.key

theorem GenDone.keep (h : GenDone p original final s) (hm : t.mem = s.mem) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : GenDone p original final t := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨g.keep hm hr hw hg, ?_, ?_, ?_⟩ <;> rw [hm]
  exacts [h1, h2, h3]

theorem keyStatus_lt (r : KeySearchResult) : r.keyStatus < 4 := by
  unfold KeySearchResult.keyStatus
  split <;> decide

end

/-- An iteration: the search, its classification and the loop's test. -/
theorem gen_iteration [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult} {n : Nat}
    (h : GenInv p original final n s) :
    WP isa (iteration (searchCall v) keyCall) s fun t =>
      (eval .e t = some false ∧ GenDone p original final t) ∨
      (eval .e t = some true ∧ ∃ m < n, GenInv p original final m t) := by
  obtain ⟨used, st, rfl, hi⟩ := h
  unfold iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (search_run v hi.1) fun t ha => ?_)
  refine WP.seq (WP.mono (classify_ok hi ha) fun u hc => ?_)
  rcases hc with ⟨-, h4, -, ⟨st', e, hl', hm, htail, -, -⟩, ⟨tr, hfin⟩⟩ | ⟨-, hd⟩
  · refine WP.mono (status_guard hl'.toGenFrame h4 (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ => Or.inr ⟨hx, _, hm, ?_⟩
    refine GenInv.keep ⟨_, st', rfl, ⟨hl', tr ++ e, ?_⟩⟩ hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
    rw [hfin, htail, consume_consume]
  · have hlt := keyStatus_lt final
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega)) fun x ⟨⟨hx, hmem⟩, k⟩ => Or.inl ⟨?_, ?_⟩
    · rw [hx]; congr 1; simp only [decide_eq_false_iff_not]; omega
    · exact hd.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))

theorem gen_loop [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult} {n : Nat}
    (h : GenInv p original final n s) :
    WP isa (.loop (iteration (searchCall v) keyCall) .e) s (GenDone p original final) :=
  WP.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .e) (Q := GenDone p original final)
    (GenInv p original final) (fun _ _ h => gen_iteration v h) n s h

end VG.Proof.RsaKeyGen.X86_64.Generate
