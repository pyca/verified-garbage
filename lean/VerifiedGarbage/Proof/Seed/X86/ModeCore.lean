module

public import VerifiedGarbage.Proof.Seed.ModeCipher
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Seed.X86.Modes
import VerifiedGarbage.Proof.Seed.X86.EcbCall
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Seed.X86.Ecb
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Seed.X86.Verified
public meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# SEED's core for the modes on x86 (32-bit)

`dirCoreSpec d`: SEED's core for the direction `d` (`Impl.Seed.X86.dirCore d`)
meets what the modes need of a core (`Proof.Modes.X86.CoreSpec`), with the
key a schedule, read in place through the first stack argument, its cipher
`Proof.Seed.dirCipher d`. The schedule and that argument are readable and
apart from every writable region and from the core's 20 bytes of stack
(`KeyIn`), so nothing the modes or the core write changes them; the fifth
argument, the scratch buffer's address, likewise (`ScrArg`).

`crypt` calls the blocks function on the buffer's block (`WP.callWith`,
with ECB's code, `ecb_correct`), in a frame of its arguments, which with the
call's return address are the core's 20 bytes of stack, apart from the
scratch buffer; the function restores `esi` and `ebp`, which the core
stores back to the modes' slots (the words they were loaded from, so memory
is as the call left it), and `edi` comes back from the fifth argument.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.X86.Wp VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (argOp sb)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout write4_apply)
open VG.Proof.Seed (dirCipher dirCipher_bytes dirKeys bytesAt_eq ecbX86)
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

/-- The schedule `k`, at the address in the first stack argument: readable,
and apart from every writable region and from the 20 bytes below `esp`, as
is that argument. -/
def KeyIn (s : State) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.Seed.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 128 ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, Region.Disjoint ⟨p.setWidth 64, 128⟩ r) ∧
    (∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨p.setWidth 64, 128⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨s.ea (argOp 0), 4⟩

/-- The fifth stack argument holds `q` and is apart from every writable
region and from the 20 bytes below `esp`. -/
def ScrArg (s : State) (q : BitVec 32) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (argOp 4)) 4 ∧ s.mem.readW (s.ea (argOp 4)) 32 = q ∧
    (∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 4), 4⟩ r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨s.ea (argOp 4), 4⟩

/-- The key's arguments, the regions `rs` writable, each at the scratch
buffer's address (the fifth argument), and apart from the core's stack. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  KeyIn s k ∧ ∃ q : BitVec 32, ScrArg s q ∧ (∀ r ∈ rs, r ∈ s.wr) ∧ (∀ r ∈ rs, r.base = q.setWidth 64) ∧
    ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) 20) r

/-- The key ready, with the scratch buffer at `B`. -/
def Ready (s : State) (B : BitVec 32) (k : Spec.Seed.Schedule) : Prop :=
  KeyIn s k ∧ ScrArg s B ∧ B.toNat + 4 * (coreSlots + 10) ≤ 2 ^ 32 ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨B.setWidth 64, 4 * (coreSlots + 10)⟩

theorem dirCore_total (d : Direction) : (dirCore d).total = 286 := rfl
theorem dirCore_slots (d : Direction) : (dirCore d).slots = 276 := rfl

theorem ea_congr {s s' : State} (h : s'.gpr .esp = s.gpr .esp) (i : Nat) : s'.ea (argOp i) = s.ea (argOp i) := by
  show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [h]

theorem keyIn_frame {s s' : State} {k : Spec.Seed.Schedule} {rs : List Region} (h : KeyIn s k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hk : ∀ r ∈ rs, Region.Disjoint (⟨s.mem.readW (s.ea (argOp 0)) 32 |>.setWidth 64, 128⟩ : Region) r)
    (ha : ∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) : KeyIn s' k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis, hsK, hsA⟩ := h
  rw [hp] at hk
  refine ⟨p, by rw [hrd, hwr, ea_congr hesp]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit,
    by rw [hwr]; exact hdis, by rw [hwr, ea_congr hesp]; exact hadis, by rw [hesp]; exact hsK,
    by rw [hesp, ea_congr hesp]; exact hsA⟩
  · rw [ea_congr hesp, hf.readW (Region.contains_self _ _) ha (by decide), hp]
  · exact (Proof.Seed.scheduleAt_frame hf hk).symm

theorem scrArg_frame {s s' : State} {q : BitVec 32} {rs : List Region} (h : ScrArg s q)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 4), 4⟩ r) : ScrArg s' q := by
  obtain ⟨hin, hq, hdis, hst⟩ := h
  refine ⟨by rw [hrd, hwr, ea_congr hesp]; exact hin, ?_, by rw [hwr, ea_congr hesp]; exact hdis,
    by rw [hesp, ea_congr hesp]; exact hst⟩
  rw [ea_congr hesp, hf.readW (Region.contains_self _ _) ha (by decide), hq]

/-- Regions within writable ones are apart from what is apart from every
writable region. -/
theorem disj_sub {s : State} {R : Region} {rs : List Region} (h : ∀ r ∈ s.wr, Region.Disjoint R r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : ∀ r ∈ rs, Region.Disjoint R r := fun r hr => by
  obtain ⟨r', hr', hsub⟩ := hs r hr
  exact (h r' hr').sub_right hsub

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨hk, q, hq, hin, hbase, hst⟩ := h
  have hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r' := fun r hr => ⟨r, hin r hr, fun _ h => h⟩
  obtain ⟨p, -, hp, -, -, -, hdis, hadis, -, -⟩ := id hk
  refine ⟨keyIn_frame hk hesp hrd hwr hf (by rw [hp]; exact disj_sub hdis hs) (disj_sub hadis hs), q,
    scrArg_frame hq hesp hrd hwr hf (disj_sub hq.2.2.1 hs), by rw [hwr]; exact hin, hbase,
    by rw [hesp]; exact hst⟩

theorem prepare_wp (d : Direction) {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (_ : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B k ∧ s'.gpr VG.Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hkey, q, hq, -, hbase, hst⟩ := hk
  have hqB : q = B := by
    have h1 : B.setWidth 64 = q.setWidth 64 := hbase _ hR
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h1
    rw [toNat_setWidth32, toNat_setWidth32] at this
    exact this.symm
  subst hqB
  exact WP.block_nil ⟨⟨hkey, hq, hs.fit, hst _ hR⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## The call -/

/-- Writing back the word read from `a` changes nothing. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  rw [write4_apply]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

theorem modeDSlot_eq : modeDSlot = 280 := rfl
theorem modeNSlot_eq : modeNSlot = 281 := rfl
theorem bufSlot_eq : bufSlot = 272 := rfl

/-- The one block ECB transforms. -/
theorem block_of_ecb {d : Direction} {m m' : Mem} {K : Spec.Seed.Schedule} {P : Addr}
    (h : Spec.Seed.blocksAt m' P 1 = Spec.Seed.ecb K d (Spec.Seed.blocksAt m P 1)) :
    Spec.Seed.blockAt m' P = Spec.Seed.crypt (dirKeys d K) (Spec.Seed.blockAt m P) := by
  cases d <;> simpa [Spec.Seed.blocksAt, Spec.Seed.ecb, Spec.Seed.encryptBlock, Spec.Seed.decryptBlock,
    dirKeys] using h

theorem crypt_wp (d : Direction) {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hr : Ready s B k) (hst : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Ready s' B k ∧ Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hkey, ⟨hin4, h4, hw4, hs4⟩, hfB, hsS⟩ := hr
  obtain ⟨p, hin0, hp, rfl, hsch, hfitK, hwK, hwA, hsK, hsA⟩ := id hkey
  have hw := hs.wr
  rw [dirCore_total] at hw
  have hst' : 20 ≤ (s.gpr .esp).toNat := hst
  have hB' : s.gpr .edi = B := hB
  have hE := (s.gpr .esp).isLt
  have hfB' : B.toNat + 4 * 286 ≤ 2 ^ 32 := hfB
  have slotIn : ∀ o, o + 4 ≤ 4 * 286 → (⟨B.setWidth 64, 4 * 286⟩ : Region).Contains (addr B o) 4 := fun o h => by
    rw [addr_eq (by omega_arith)]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hK : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 4 * 286⟩ := hwK _ hw
  show WP isa (cryptCall d) s _
  unfold cryptCall callHead
  refine WP.seq ?_
  refine wp_ldm (b := .edi) (o := 4 * modeDSlot) hB'
    ⟨_, List.mem_append_right _ hw, slotIn _ (by rw [modeDSlot_eq]; omega_arith)⟩
    fun s₁ u₁ => wp_ldm (b := .edi) (o := 4 * modeNSlot) ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr]; exact ⟨_, List.mem_append_right _ hw, slotIn _ (by rw [modeNSlot_eq]; omega_arith)⟩)
    fun s₂ u₂ => wp_ldm (b := .esp) (o := 4) (B := s.gpr .esp)
      ((u₂.other _ (by decide)).trans (u₁.other _ (by decide)))
      (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin0)
    fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have g₆ : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have esp₆ : s₆.gpr .esp = s.gpr .esp := g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have edi₆ : s₆.gpr .edi = B := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB'
  have eax₆ : s₆.gpr .eax = p := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
    exact hp
  have ecx₆ : s₆.gpr .ecx = B + BitVec.ofNat 32 (4 * bufSlot) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
    exact congrArg (· + BitVec.ofNat 32 (4 * bufSlot)) hB'
  have edx₆ : s₆.gpr .edx = 1 := u₆.gpr
  have esi₆ : s₆.gpr .esi = s.mem.readW (addr B (4 * modeDSlot)) 32 := by
    rw [g₆ .esi |> fun _ => u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ebp₆ : s₆.gpr .ebp = s.mem.readW (addr B (4 * modeNSlot)) 32 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.mem]
  -- The call.
  have hrs : Reg.esp ∉ [Reg.edi, .edx, .ecx, .eax] := by decide
  have fit : 4 * [Reg.edi, .edx, .ecx, .eax].length + 4 ≤ (s₆.gpr .esp).toNat := by
    rw [esp₆]; show 20 ≤ _; omega_arith
  have a0 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0 = p := by
    rw [callEntry_arg fit hrs (i := 0) (by decide)]; exact eax₆
  have a1 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 1 = B + BitVec.ofNat 32 (4 * bufSlot) := by
    rw [callEntry_arg fit hrs (i := 1) (by decide)]; exact ecx₆
  have a2 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 2 = 1 := by
    rw [callEntry_arg fit hrs (i := 2) (by decide)]; exact edx₆
  have a3 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 3 = B := by
    rw [callEntry_arg fit hrs (i := 3) (by decide)]; exact edi₆
  have espE : ((pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 20 := by
    rw [callEntry_espNat fit, esp₆]; rfl
  have argsE : (⟨argAddr (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0, 16⟩ : Region) =
      below (s₆.gpr .esp) 16 := by
    rw [callEntry_argAddr0]; rfl
  have argsSub : Region.Sub ⟨argAddr (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0, 16⟩
      (stkRegion (s.gpr .esp) 20) := by
    rw [argsE, esp₆]; exact below_sub (by decide) hst'
  have retSub : Region.Sub ⟨((pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.gpr .esp).setWidth 64, 4⟩
      (stkRegion (s.gpr .esp) 20) := by
    rw [show (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.gpr .esp =
        s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [callEntry_esp', esp₆, BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
    exact below_inner (a := 4) (k := 16) (b := 20) (by decide) hst'
  have hbufA : (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (4 * bufSlot) :=
    addr_eq (by rw [bufSlot_eq]; omega_arith)
  have bufSub : Region.Sub ⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩ ⟨B.setWidth 64, 4 * 286⟩ := by
    rw [hbufA]; exact VG.Offset.sub_base _ (by rw [bufSlot_eq]; omega_arith)
  have wsSub : Region.Sub ⟨B.setWidth 64, 4 * wsSlots⟩ ⟨B.setWidth 64, 4 * 286⟩ := Region.sub_prefix (by decide)
  have bufWs : Region.Disjoint ⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩ ⟨B.setWidth 64, 4 * wsSlots⟩ := by
    rw [hbufA]; exact VG.Offset.disjoint_base _ (by rw [bufSlot_eq]; decide) (by rw [bufSlot_eq]; omega_arith)
  have fE : Frame [stkRegion (s.gpr .esp) 20] s.mem (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.mem := by
    have := callEntry_frame fit hrs
    rw [esp₆, m₆] at this
    exact this
  have hblkE : Spec.Seed.blockAt (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.mem
      ((B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) =
      Spec.Seed.blockAt s.mem ((B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) := by
    have := Proof.Seed.blocksAt_frame fE (p := (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) (n := 1)
      (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (hsS.sub_right (by rw [Nat.mul_comm] at bufSub ⊢; exact bufSub)).symm) (by decide)
    simpa [Spec.Seed.blocksAt] using this
  have hschE : Spec.Seed.scheduleAt (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.mem (p.setWidth 64) =
      Spec.Seed.scheduleAt s.mem (p.setWidth 64) :=
    Proof.Seed.scheduleAt_frame fE fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hsK.symm
  have hbuf32 : (B + BitVec.ofNat 32 (4 * bufSlot)).toNat = B.toNat + 4 * bufSlot := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * bufSlot) (by rw [bufSlot_eq]; decide),
      Nat.mod_eq_of_lt (by rw [bufSlot_eq]; omega_arith)]
  have ha : ∀ d' : Direction, blkAddr (dirCore d') B 0 = (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64 :=
    fun _ => by rw [hbufA]; simp only [blkAddr, dirCore, Nat.mul_zero, BitVec.add_zero]
  have hbw : ∀ d' : Direction, 4 * (dirCore d').bw = 16 := fun _ => rfl
  refine WP.seq ?_
  cases d <;>
  · refine WP.callWith (k := ecbX86 _) (ecb_correct _) (ecb_noSp _) (by decide) hrs
      (by rw [ecb_stackUse, esp₆]; show 20 ≤ _; omega_arith)
      (rd := [⟨p.setWidth 64, 128⟩, ⟨argAddr (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0, 16⟩])
      (wr := [⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩, ⟨B.setWidth 64, 4 * wsSlots⟩])
      ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs f ⟨s₃', m₃', post⟩ => ?_
    · simp only [ecbX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
        argAddr_withRegions, a0, a1, a2, a3]
      refine ⟨trivial, rfl, hK.sub_right bufSub, hK.sub_right wsSub, bufWs, ?_, ?_, ?_, ?_, hfitK, ?_,
        by rw [show wsSlots = 272 from rfl]; omega_arith, by rw [espE]; omega_arith⟩
      · exact (hsS.sub_right bufSub).sub_left argsSub
      · exact (hsS.sub_right wsSub).sub_left argsSub
      · exact (hsS.sub_right bufSub).sub_left retSub
      · exact (hsS.sub_right wsSub).sub_left retSub
      · rw [hbuf32, bufSlot_eq, show (1 : BitVec 32).toNat = 1 from rfl]; omega_arith
    · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.right (Covers.of_sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rcases List.mem_append.mp hsch with h | h
          · exact List.mem_append_left _ (by rw [rd₆]; exact h)
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [wr₆]; exact h))
        · rw [argsE]; exact List.mem_append_right _ List.mem_cons_self
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 4 * bufSlot, hbufA,
            by show 4 * 272 + 16 * 1 ≤ 4 * 286; decide⟩
        · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 0, by simp,
            by show 0 + 4 * 272 ≤ 4 * 286; decide⟩
    · refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 4 * bufSlot, hbufA,
          by show 4 * 272 + 16 * 1 ≤ 4 * 286; decide⟩
      · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 0, by simp, by show 0 + 4 * 272 ≤ 4 * 286; decide⟩
    -- After the call.
    · simp only [ecb_stackUse, List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at f
      simp only [ecbX86, State.withRegions_mem, arg_withRegions, a0, a1, a2, m₃'] at post
      have esp' : s'.gpr .esp = s.gpr .esp := (cs .esp (by decide)).trans esp₆
      have rd'' : s'.rd = s.rd := rd'.trans rd₆
      have wr'' : s'.wr = s.wr := wr'.trans wr₆
      have fr' : Frame [⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩, ⟨B.setWidth 64, 4 * wsSlots⟩,
          stkRegion (s.gpr .esp) 20] s.mem s'.mem := by
        rw [← m₆]
        have e : below (s₆.gpr .esp) 20 = stkRegion (s.gpr .esp) 20 := by rw [esp₆]
        rw [e] at f
        exact f
      have outSlot : ∀ o, 4 * coreSlots ≤ o → o + 4 ≤ 4 * 286 →
          ∀ r ∈ [(⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩ : Region), ⟨B.setWidth 64, 4 * wsSlots⟩,
            stkRegion (s.gpr .esp) 20], Region.Disjoint ⟨addr B o, 4⟩ r := fun o h₁ h₂ r hr => by
        rw [addr_eq (by omega_arith)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hbufA]
          exact (VG.Offset.disjoint _ (.inr (by rw [bufSlot_eq]; simp only [coreSlots, bufSlot_eq] at h₁; omega_arith))
            (by omega_arith) (by rw [bufSlot_eq]; omega_arith))
        · exact VG.Offset.disjoint_base _ (by simp only [coreSlots, bufSlot_eq, wsSlots] at h₁ ⊢; omega_arith)
            (by omega_arith)
        · exact (hsS.sub_right (VG.Offset.sub_base _ (by rw [show coreSlots + 10 = 286 from rfl]; omega_arith))).symm
      have keepD : s'.mem.readW (addr B (4 * modeDSlot)) 32 = s.mem.readW (addr B (4 * modeDSlot)) 32 :=
        fr'.readW (Region.contains_self _ _) (outSlot _ (by rw [modeDSlot_eq]; decide)
          (by rw [modeDSlot_eq]; omega_arith)) (by decide)
      have keepN : s'.mem.readW (addr B (4 * modeNSlot)) 32 = s.mem.readW (addr B (4 * modeNSlot)) 32 :=
        fr'.readW (Region.contains_self _ _) (outSlot _ (by rw [modeNSlot_eq]; decide)
          (by rw [modeNSlot_eq]; omega_arith)) (by decide)
      have hs' : ∀ r ∈ [(⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩ : Region),
          ⟨B.setWidth 64, 4 * wsSlots⟩], ∃ r' ∈ s.wr, Region.Sub r r' := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, hw, bufSub⟩
        · exact ⟨_, hw, wsSub⟩
      have dis3 : ∀ {R : Region}, (∀ r ∈ s.wr, Region.Disjoint R r) → Region.Disjoint (stkRegion (s.gpr .esp) 20) R →
          ∀ r ∈ [(⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩ : Region), ⟨B.setWidth 64, 4 * wsSlots⟩,
            stkRegion (s.gpr .esp) 20], Region.Disjoint R r := fun hW hS r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact disj_sub hW hs' _ List.mem_cons_self
        rcases List.mem_cons.mp hr with rfl | hr
        · exact disj_sub hW hs' _ (List.mem_cons_of_mem _ List.mem_cons_self)
        rw [List.mem_singleton] at hr; subst hr; exact hS.symm
      have q' : s'.mem.readW (s.ea (argOp 4)) 32 = B := by
        rw [fr'.readW (Region.contains_self _ _) (dis3 hw4 hs4) (by decide), h4]
      unfold callTail
      refine wp_ldm (b := .esp) (o := 4 + 4 * 4) (B := s.gpr .esp) esp' (by rw [rd'', wr'']; exact hin4)
        fun s₇ u₇ => ?_
      have edi₇ : s₇.gpr .edi = B := u₇.gpr.trans q'
      have inD : InRegions s₇.wr (addr B (4 * modeDSlot)) 4 := by
        rw [u₇.wr, wr'']; exact ⟨_, hw, slotIn _ (by rw [modeDSlot_eq]; omega_arith)⟩
      refine wp_stm (b := .edi) (B := B) (o := 4 * modeDSlot) edi₇ inD fun s₈ u₈ => ?_
      have inN : InRegions s₈.wr (addr B (4 * modeNSlot)) 4 := by
        rw [u₈.wr, u₇.wr, wr'']; exact ⟨_, hw, slotIn _ (by rw [modeNSlot_eq]; omega_arith)⟩
      refine wp_stm (b := .edi) (B := B) (o := 4 * modeNSlot) ((congrFun u₈.gpr _).trans edi₇) inN
        fun s₉ u₉ => WP.block_nil ?_
      have m₉ : s₉.mem = s'.mem := by
        rw [u₉.mem, u₈.gpr, u₈.mem, u₇.mem, u₇.other _ (by decide), u₇.other _ (by decide), cs .esi (by decide),
          cs .ebp (by decide), esi₆, ebp₆, ← keepD, writeW_readW, ← keepN, writeW_readW]
      have g₉ : ∀ r, s₉.gpr r = s₇.gpr r := fun r => by rw [u₉.gpr, u₈.gpr]
      have esp₉ : s₉.gpr .esp = s.gpr .esp := by rw [g₉, u₇.other _ (by decide), esp']
      have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd'']
      have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr'']
      have fr₉ : Frame [⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 1⟩, ⟨B.setWidth 64, 4 * wsSlots⟩,
          stkRegion (s.gpr .esp) 20] s.mem s₉.mem := by rw [m₉]; exact fr'
      refine ⟨by rw [g₉]; exact edi₇, esp₉, ⟨keyIn_frame hkey esp₉ rd₉ wr₉ fr₉ (by rw [hp]; exact dis3 hwK hsK)
          (dis3 hwA hsA), scrArg_frame ⟨hin4, h4, hw4, hs4⟩ esp₉ rd₉ wr₉ fr₉ (dis3 hw4 hs4), hfB,
          by rw [esp₉]; exact hsS⟩, ?_, fun j hj => ?_, rd₉, wr₉⟩
      · refine fr₉.sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · refine ⟨_, List.mem_cons_self, ?_⟩
          rw [hbufA]; exact VG.Offset.sub_base _ (by simp only [dirCore, coreSlots, bufSlot_eq]; omega_arith)
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, coreSlots, bufSlot_eq]; decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · have hj0 : j = 0 := by simp only [dirCore] at hj; omega_arith
        subst hj0
        rw [show (1 : BitVec 32).toNat = 1 from rfl] at post
        have hb := block_of_ecb post
        rw [hschE, hblkE] at hb
        rw [hbw, ha, dirCipher_bytes, bytesAt_eq, m₉, hb]

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, dirCore]
  layout := ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame {s s' B k rs} h e r w _ hf hs _ := by
    obtain ⟨hk, hq, hfB, hst⟩ := h
    obtain ⟨p, -, hp, -, -, -, hdis, hadis, -, -⟩ := id hk
    exact ⟨keyIn_frame hk e r w hf (by rw [hp]; exact disj_sub hdis hs) (disj_sub hadis hs),
      scrArg_frame hq e r w hf (disj_sub hq.2.2.1 hs), hfB, by rw [e]; exact hst⟩
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Seed.X86
