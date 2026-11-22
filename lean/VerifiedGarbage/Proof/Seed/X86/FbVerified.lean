module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.X86.Modes
import VerifiedGarbage.Proof.Modes.X86.Wide
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Proof.Modes.X86.Seq
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Seed.X86.FbLit
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.X86.Inline
public meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Seed.X86.FbLit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Seed.X86.Prologue
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Seed.X86.Prologue
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Seed.ModeBytes
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
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Modes.X86.Core
meta import VerifiedGarbage.Impl.Seed.X86.Modes
meta import VerifiedGarbage.Proof.Seed.X86.EcbCall
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.Seed.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Seed.X86.Verified

/-! ### `Seed.X86.ModeCore`, which only this module used -/

section

/-! ### `Seed.ModeCipher`, which only this module used -/

section

/-!
# SEED's cipher for the modes, on any target

What x86's core for the modes (`Proof/Seed/X86/FbVerified.lean`) adds to
`ModeBytes`: the cipher of a direction on the 16 bytes at `p` is
`Spec.Seed.crypt` with the schedule's round keys in that direction's order
(`dirCipher_bytes`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG
open VG.Spec.Seed (Direction)
open VG.Spec.Aes (bytesAt)

theorem ofFn_toList (v : Spec.Seed.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

/-- The round keys in the order of the direction `d`. -/
def dirKeys : Direction → Spec.Seed.Schedule → Nat → Spec.Seed.Word × Spec.Seed.Word
  | .encrypt, k => Spec.Seed.roundKey k
  | .decrypt, k => fun j => Spec.Seed.roundKey k (15 - j)

/-- The cipher of `d` on the 16 bytes at `p`: the rounds with the round keys
in `d`'s order. -/
theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) = (Spec.Seed.crypt (dirKeys d k) (Spec.Seed.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Seed.cipher, bytesAt_eq, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Seed.invCipher, bytesAt_eq, ofFn_toList]; rfl

end VG.Proof.Seed

end

end


/-!
# SEED's core for the modes on x86 (32-bit)

`dirCoreSpec d`: SEED's core for the direction `d` (`Impl.Seed.X86.dirCore d`)
meets what the modes need of a core (`Proof.Modes.X86.CoreSpec`), with the
key a schedule, read in place through the first stack argument, its cipher
`Proof.Seed.dirCipher d`. The schedule and that argument are readable and
apart from every writable region and from the core's 20 bytes of stack
(`KeyIn`), so nothing the modes or the core write changes them; the fifth
argument, the scratch buffer's address, likewise (`ScrArg`).

`crypt` calls the blocks function on the buffer's eight blocks, with the
scratch buffer's first `modeWs` slots for its working space (`WP.callWith`,
with ECB's code, `ecb_correctW`), in a frame of its arguments, which with the
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
open VG.Proof.Seed (dirCipher dirCipher_bytes dirKeys bytesAt_eq ecbX86W)
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
  obtain hs : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r' := fun r hr => ⟨r, hin r hr, fun _ h => h⟩
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
  obtain hqB : q = B := by
    obtain h1 : B.setWidth 64 = q.setWidth 64 := hbase _ hR
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
theorem bufSlot_eq : bufSlot = 244 := rfl
theorem modeWs_eq : modeWs = 244 := rfl

/-- Block `j` of those ECB transforms. -/
theorem block_of_ecb {d : Direction} {m m' : Mem} {K : Spec.Seed.Schedule} {P : Addr} {n j : Nat} (hj : j < n)
    (h : Spec.Seed.blocksAt m' P n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m P n)) :
    Spec.Seed.blockAt m' (P + BitVec.ofNat 64 (16 * j)) =
      Spec.Seed.crypt (dirKeys d K) (Spec.Seed.blockAt m (P + BitVec.ofNat 64 (16 * j))) := by
  have e := congrArg (·[j]?) h
  cases d <;> simpa [Spec.Seed.blocksAt, Spec.Seed.ecb, Spec.Seed.encryptBlock, Spec.Seed.decryptBlock,
    dirKeys, hj] using e

theorem cryptFrame_wp (d : Direction) {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hr : Ready s B k) (hst : (dirCore d).stack ≤ (s.gpr .esp).toNat)
    (hfl : s.mem.readW (wordAddr B dirSlot) 32 = BitVec.ofNat 32 (dirFlag d)) :
    WP isa blocksFrame s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
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
  obtain hE := (s.gpr .esp).isLt
  have hfB' : B.toNat + 4 * 286 ≤ 2 ^ 32 := hfB
  obtain slotIn : ∀ o, o + 4 ≤ 4 * 286 → (⟨B.setWidth 64, 4 * 286⟩ : Region).Contains (addr B o) 4 := fun o h => by
    rw [addr_eq (by omega_arith)]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain hK : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 4 * 286⟩ := hwK _ hw
  unfold blocksFrame callHead
  refine WP.seq ?_
  refine wp_ldm (b := .edi) (o := 4 * modeDSlot) hB'
    ⟨_, List.mem_append_right _ hw, slotIn _ (by rw [modeDSlot_eq]; omega_arith)⟩
    fun s₁ u₁ => wp_ldm (b := .edi) (o := 4 * modeNSlot) ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr]; exact ⟨_, List.mem_append_right _ hw, slotIn _ (by rw [modeNSlot_eq]; omega_arith)⟩)
    fun s₂ u₂ => wp_ldm (b := .esp) (o := 4) (B := s.gpr .esp)
      ((u₂.other _ (by decide)).trans (u₁.other _ (by decide)))
      (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin0)
    fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain g₆ : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  obtain esp₆ : s₆.gpr .esp = s.gpr .esp := g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain edi₆ : s₆.gpr .edi = B := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB'
  obtain eax₆ : s₆.gpr .eax = p := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
    exact hp
  obtain ecx₆ : s₆.gpr .ecx = B + BitVec.ofNat 32 (4 * bufSlot) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
    exact congrArg (· + BitVec.ofNat 32 (4 * bufSlot)) hB'
  have edx₆ : s₆.gpr .edx = 8 := u₆.gpr
  obtain esi₆ : s₆.gpr .esi = s.mem.readW (addr B (4 * modeDSlot)) 32 := by
    rw [g₆ .esi |> fun _ => u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  obtain ebp₆ : s₆.gpr .ebp = s.mem.readW (addr B (4 * modeNSlot)) 32 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.mem]
  -- The call.
  obtain hrs : Reg.esp ∉ [Reg.edi, .edx, .ecx, .eax] := by decide
  obtain fit : 4 * [Reg.edi, .edx, .ecx, .eax].length + 4 ≤ (s₆.gpr .esp).toNat := by
    rw [esp₆]; show 20 ≤ _; omega_arith
  obtain a0 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0 = p := by
    rw [callEntry_arg fit hrs (i := 0) (by decide)]; exact eax₆
  obtain a1 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 1 = B + BitVec.ofNat 32 (4 * bufSlot) := by
    rw [callEntry_arg fit hrs (i := 1) (by decide)]; exact ecx₆
  obtain a2 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 2 = 8 := by
    rw [callEntry_arg fit hrs (i := 2) (by decide)]; exact edx₆
  obtain a3 : arg (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 3 = B := by
    rw [callEntry_arg fit hrs (i := 3) (by decide)]; exact edi₆
  obtain espE : ((pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 20 := by
    rw [callEntry_espNat fit, esp₆]; rfl
  obtain argsE : (⟨argAddr (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0, 16⟩ : Region) =
      below (s₆.gpr .esp) 16 := by
    rw [callEntry_argAddr0]; rfl
  obtain argsSub : Region.Sub ⟨argAddr (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0, 16⟩
      (stkRegion (s.gpr .esp) 20) := by
    rw [argsE, esp₆]; exact below_sub (by decide) hst'
  obtain retSub : Region.Sub ⟨((pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.gpr .esp).setWidth 64, 4⟩
      (stkRegion (s.gpr .esp) 20) := by
    rw [show (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.gpr .esp =
        s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [callEntry_esp', esp₆, BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
    exact below_inner (a := 4) (k := 16) (b := 20) (by decide) hst'
  obtain hbufA : (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (4 * bufSlot) :=
    addr_eq (by rw [bufSlot_eq]; omega_arith)
  obtain bufSub : Region.Sub ⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩ ⟨B.setWidth 64, 4 * 286⟩ := by
    rw [hbufA]; exact VG.Offset.sub_base _ (by rw [bufSlot_eq]; omega_arith)
  obtain wsSub : Region.Sub ⟨B.setWidth 64, 4 * modeWs⟩ ⟨B.setWidth 64, 4 * 286⟩ := Region.sub_prefix (by decide)
  obtain bufWs : Region.Disjoint ⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩ ⟨B.setWidth 64, 4 * modeWs⟩ := by
    rw [hbufA]; exact VG.Offset.disjoint_base _ (by rw [bufSlot_eq]; decide) (by rw [bufSlot_eq]; omega_arith)
  obtain fE : Frame [stkRegion (s.gpr .esp) 20] s.mem (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.mem := by
    have := callEntry_frame fit hrs
    rw [esp₆, m₆] at this
    exact this
  obtain hblkE : Spec.Seed.blocksAt (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.mem
      ((B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) 8 =
      Spec.Seed.blocksAt s.mem ((B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) 8 :=
    Proof.Seed.blocksAt_frame fE (p := (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) (n := 8)
      (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (hsS.sub_right bufSub).symm) (by decide)
  obtain hschE : Spec.Seed.scheduleAt (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry.mem (p.setWidth 64) =
      Spec.Seed.scheduleAt s.mem (p.setWidth 64) :=
    Proof.Seed.scheduleAt_frame fE fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hsK.symm
  obtain hbuf32 : (B + BitVec.ofNat 32 (4 * bufSlot)).toNat = B.toNat + 4 * bufSlot := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * bufSlot) (by rw [bufSlot_eq]; decide),
      Nat.mod_eq_of_lt (by rw [bufSlot_eq]; omega_arith)]
  obtain ha : ∀ (d' : Direction) (j : Nat), blkAddr (dirCore d') B j =
      (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64 + BitVec.ofNat 64 (16 * j) :=
    fun _ _ => by rw [hbufA]; rfl
  obtain hbw : ∀ d' : Direction, 4 * (dirCore d').bw = 16 := fun _ => rfl
  refine WP.seq ?_
  · refine WP.callWith (k := ecbX86W modeWs d) (ecb_correctW d (by decide)) blocks_noSp (by decide) hrs
      (by rw [ecb_stackUse, esp₆]; show 20 ≤ _; omega_arith)
      (rd := [⟨p.setWidth 64, 128⟩, ⟨argAddr (pushed [Reg.edi, .edx, .ecx, .eax] s₆).callEntry 0, 16⟩])
      (wr := [⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩, ⟨B.setWidth 64, 4 * modeWs⟩])
      ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs f ⟨s₃', m₃', post⟩ => ?_
    · simp only [ecbX86W, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
        argAddr_withRegions, State.withRegions_mem, a0, a1, a2, a3]
      refine ⟨trivial, rfl, hK.sub_right bufSub, hK.sub_right wsSub, bufWs, ?_, ?_, ?_, ?_, hfitK, ?_,
        by rw [modeWs_eq]; omega_arith, by rw [espE]; omega_arith, ?_⟩
      · exact (hsS.sub_right bufSub).sub_left argsSub
      · exact (hsS.sub_right wsSub).sub_left argsSub
      · exact (hsS.sub_right bufSub).sub_left retSub
      · exact (hsS.sub_right wsSub).sub_left retSub
      · rw [hbuf32, bufSlot_eq, show (8 : BitVec 32).toNat = 8 from rfl]; omega_arith
      · rw [fE.readW (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          exact (hsS.sub_right (show Region.Sub ⟨addr B (4 * dirSlot), 4⟩ ⟨B.setWidth 64, 4 * 286⟩ by
            rw [addr_eq (by rw [dirSlot, ptrSlot_eq]; omega_using [hfB'])]
            exact VG.Offset.sub_base _ (by decide))).symm) (by decide)]
        exact hfl
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
            by show 4 * 244 + 16 * 8 ≤ 4 * 286; decide⟩
        · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 0, by simp,
            by show 0 + 4 * 244 ≤ 4 * 286; decide⟩
    · refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 4 * bufSlot, hbufA,
          by show 4 * 244 + 16 * 8 ≤ 4 * 286; decide⟩
      · exact ⟨⟨B.setWidth 64, 4 * 286⟩, List.mem_cons_of_mem _ (by rw [wr₆]; exact hw), 0, by simp, by show 0 + 4 * 244 ≤ 4 * 286; decide⟩
    -- After the call.
    · simp only [ecb_stackUse, List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at f
      simp only [ecbX86W, State.withRegions_mem, arg_withRegions, a0, a1, a2] at post
      obtain hblk₃ : Spec.Seed.blocksAt s'.mem ((B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) 8 =
          Spec.Seed.blocksAt s₃'.mem ((B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) 8 := by
        have f₃ : Frame [stkRegion (s.gpr .esp) 20] s₃'.mem s'.mem := by
          have := Frame.below_mono (wr := []) m₃' (b := 20) (by decide) fit
          rw [esp₆] at this; exact this
        exact Proof.Seed.blocksAt_frame f₃ (p := (B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64) (n := 8)
          (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr
            exact (hsS.sub_right bufSub).symm) (by decide)
      obtain esp' : s'.gpr .esp = s.gpr .esp := (cs .esp (by decide)).trans esp₆
      obtain rd'' : s'.rd = s.rd := rd'.trans rd₆
      obtain wr'' : s'.wr = s.wr := wr'.trans wr₆
      obtain fr' : Frame [⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩, ⟨B.setWidth 64, 4 * modeWs⟩,
          stkRegion (s.gpr .esp) 20] s.mem s'.mem := by
        rw [← m₆]
        obtain e : below (s₆.gpr .esp) 20 = stkRegion (s.gpr .esp) 20 := by rw [esp₆]
        rw [e] at f
        exact f
      obtain outSlot : ∀ o, 4 * coreSlots ≤ o → o + 4 ≤ 4 * 286 →
          ∀ r ∈ [(⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩ : Region), ⟨B.setWidth 64, 4 * modeWs⟩,
            stkRegion (s.gpr .esp) 20], Region.Disjoint ⟨addr B o, 4⟩ r := fun o h₁ h₂ r hr => by
        rw [addr_eq (by omega_arith)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hbufA]
          exact (VG.Offset.disjoint _ (.inr (by rw [bufSlot_eq]; simp only [coreSlots, bufSlot_eq] at h₁; omega_arith))
            (by omega_arith) (by rw [bufSlot_eq]; omega_arith))
        · exact VG.Offset.disjoint_base _ (by simp only [coreSlots, bufSlot_eq, modeWs_eq] at h₁ ⊢; omega_arith)
            (by omega_arith)
        · exact (hsS.sub_right (VG.Offset.sub_base _ (by rw [show coreSlots + 10 = 286 from rfl]; omega_arith))).symm
      obtain keepD : s'.mem.readW (addr B (4 * modeDSlot)) 32 = s.mem.readW (addr B (4 * modeDSlot)) 32 :=
        fr'.readW (Region.contains_self _ _) (outSlot _ (by rw [modeDSlot_eq]; decide)
          (by rw [modeDSlot_eq]; omega_arith)) (by decide)
      obtain keepN : s'.mem.readW (addr B (4 * modeNSlot)) 32 = s.mem.readW (addr B (4 * modeNSlot)) 32 :=
        fr'.readW (Region.contains_self _ _) (outSlot _ (by rw [modeNSlot_eq]; decide)
          (by rw [modeNSlot_eq]; omega_arith)) (by decide)
      obtain hs' : ∀ r ∈ [(⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩ : Region),
          ⟨B.setWidth 64, 4 * modeWs⟩], ∃ r' ∈ s.wr, Region.Sub r r' := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, hw, bufSub⟩
        · exact ⟨_, hw, wsSub⟩
      obtain dis3 : ∀ {R : Region}, (∀ r ∈ s.wr, Region.Disjoint R r) → Region.Disjoint (stkRegion (s.gpr .esp) 20) R →
          ∀ r ∈ [(⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩ : Region), ⟨B.setWidth 64, 4 * modeWs⟩,
            stkRegion (s.gpr .esp) 20], Region.Disjoint R r := fun hW hS r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact disj_sub hW hs' _ List.mem_cons_self
        rcases List.mem_cons.mp hr with rfl | hr
        · exact disj_sub hW hs' _ (List.mem_cons_of_mem _ List.mem_cons_self)
        rw [List.mem_singleton] at hr; subst hr; exact hS.symm
      obtain q' : s'.mem.readW (s.ea (argOp 4)) 32 = B := by
        rw [fr'.readW (Region.contains_self _ _) (dis3 hw4 hs4) (by decide), h4]
      unfold callTail
      refine wp_ldm (b := .esp) (o := 4 + 4 * 4) (B := s.gpr .esp) esp' (by rw [rd'', wr'']; exact hin4)
        fun s₇ u₇ => ?_
      obtain edi₇ : s₇.gpr .edi = B := u₇.gpr.trans q'
      obtain inD : InRegions s₇.wr (addr B (4 * modeDSlot)) 4 := by
        rw [u₇.wr, wr'']; exact ⟨_, hw, slotIn _ (by rw [modeDSlot_eq]; omega_arith)⟩
      refine wp_stm (b := .edi) (B := B) (o := 4 * modeDSlot) edi₇ inD fun s₈ u₈ => ?_
      obtain inN : InRegions s₈.wr (addr B (4 * modeNSlot)) 4 := by
        rw [u₈.wr, u₇.wr, wr'']; exact ⟨_, hw, slotIn _ (by rw [modeNSlot_eq]; omega_arith)⟩
      refine wp_stm (b := .edi) (B := B) (o := 4 * modeNSlot) ((congrFun u₈.gpr _).trans edi₇) inN
        fun s₉ u₉ => WP.block_nil ?_
      obtain m₉ : s₉.mem = s'.mem := by
        rw [u₉.mem, u₈.gpr, u₈.mem, u₇.mem, u₇.other _ (by decide), u₇.other _ (by decide), cs .esi (by decide),
          cs .ebp (by decide), esi₆, ebp₆, ← keepD, writeW_readW, ← keepN, writeW_readW]
      obtain g₉ : ∀ r, s₉.gpr r = s₇.gpr r := fun r => by rw [u₉.gpr, u₈.gpr]
      obtain esp₉ : s₉.gpr .esp = s.gpr .esp := by rw [g₉, u₇.other _ (by decide), esp']
      obtain rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd'']
      obtain wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr'']
      obtain fr₉ : Frame [⟨(B + BitVec.ofNat 32 (4 * bufSlot)).setWidth 64, 16 * 8⟩, ⟨B.setWidth 64, 4 * modeWs⟩,
          stkRegion (s.gpr .esp) 20] s.mem s₉.mem := by rw [m₉]; exact fr'
      refine ⟨by rw [g₉]; exact edi₇, esp₉, ⟨keyIn_frame hkey esp₉ rd₉ wr₉ fr₉ (by rw [hp]; exact dis3 hwK hsK)
          (dis3 hwA hsA), scrArg_frame ⟨hin4, h4, hw4, hs4⟩ esp₉ rd₉ wr₉ fr₉ (dis3 hw4 hs4), hfB,
          by rw [esp₉]; exact hsS⟩, ?_, fun j hj => ?_, rd₉, wr₉⟩
      · refine fr₉.sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · refine ⟨_, List.mem_cons_self, ?_⟩
          rw [hbufA]; exact VG.Offset.sub_base _ (by simp only [dirCore, coreSlots, bufSlot_eq]; omega_arith)
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, coreSlots, bufSlot_eq, modeWs_eq]; decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · rw [show (8 : BitVec 32).toNat = 8 from rfl, hschE, hblkE, ← hblk₃] at post
        obtain hb := block_of_ecb (show j < 8 from hj) post
        rw [hbw, ha, dirCipher_bytes, bytesAt_eq, m₉, hb]

theorem crypt_wp (d : Direction) {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hr : Ready s B k) (hst : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Ready s' B k ∧ Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hB' : s.gpr .edi = B := hB
  have hw := hs.wr
  rw [dirCore_total] at hw
  obtain ⟨hk, hq, hfB, hstk⟩ := hr
  have hfB' : B.toNat + 4 * 286 ≤ 2 ^ 32 := hfB
  obtain wA : addr B (4 * dirSlot) = B.setWidth 64 + BitVec.ofNat 64 (4 * dirSlot) :=
    addr_eq (by rw [dirSlot, ptrSlot_eq]; omega_using [hfB'])
  obtain wSub : Region.Sub ⟨addr B (4 * dirSlot), 4⟩ ⟨B.setWidth 64, 4 * 286⟩ := by
    rw [wA]; exact VG.Offset.sub_base _ (by decide)
  obtain wIn : InRegions s.wr (addr B (4 * dirSlot)) 4 :=
    ⟨_, hw, by rw [wA]; exact VG.Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (cryptCall d) s _
  unfold cryptCall modeFlag
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => wp_stm (b := .edi) (B := B) (o := 4 * dirSlot) ((u₁.other _ (by decide)).trans hB')
    (by rw [u₁.wr]; exact wIn) fun s₂ u₂ => WP.block_nil ?_
  obtain m₂ : s₂.mem = s.mem.writeW (addr B (4 * dirSlot)) (BitVec.ofNat 32 (dirFlag d)) := by
    rw [u₂.mem, u₁.mem, u₁.gpr]
  obtain f₂ : Frame [⟨addr B (4 * dirSlot), 4⟩] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.gpr]; exact u₁.other r hr
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := g₂ _ (by decide)
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  obtain hs' : ∀ r ∈ [(⟨addr B (4 * dirSlot), 4⟩ : Region)], ∃ r' ∈ s.wr, Region.Sub r r' := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨_, hw, wSub⟩
  obtain ⟨p, -, hp, -, -, -, hdis, hadis, -, -⟩ := id hk
  obtain hr₂ : Ready s₂ B k :=
    ⟨keyIn_frame hk esp₂ rd₂ wr₂ f₂ (by rw [hp]; exact disj_sub hdis hs') (disj_sub hadis hs'),
      scrArg_frame hq esp₂ rd₂ wr₂ f₂ (disj_sub hq.2.2.1 hs'), hfB, by rw [esp₂]; exact hstk⟩
  obtain hfl : s₂.mem.readW (wordAddr B dirSlot) 32 = BitVec.ofNat 32 (dirFlag d) := by
    rw [m₂]; exact Mem.readW_writeW_self32 _ _ _
  refine WP.mono (cryptFrame_wp d (by show s₂.gpr .edi = B; rw [g₂ _ (by decide)]; exact hB')
      ⟨by rw [wr₂]; exact hs.wr, hs.fit⟩ hr₂ (by rw [esp₂]; exact hst) hfl)
    fun s' ⟨b', e', r', f', c', rd', wr'⟩ => ⟨b', e'.trans esp₂, r', ?_, fun j hj => ?_, rd'.trans rd₂, wr'.trans wr₂⟩
  · rw [esp₂] at f'
    refine (f₂.sub fun r hr => ?_).trans f'
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, by
      rw [wA]; exact VG.Offset.sub_base _ (by simp only [dirCore, coreSlots, bufSlot_eq, dirSlot, ptrSlot_eq]; decide)⟩
  · rw [c' j hj]
    have hj8 : j < 8 := hj
    congr 1
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi : i < 16 := List.mem_range.mp hi
    exact f₂.bytes (R := ⟨blkAddr (dirCore d) B j, 16⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [wA]
      simp only [blkAddr, dirCore, VG.Offset.add_add]
      exact VG.Offset.disjoint _ (.inr (by rw [bufSlot_eq, dirSlot, ptrSlot_eq]; omega_arith))
        (by rw [bufSlot_eq]; omega_arith) (by decide)) (by show 16 ≤ 2 ^ 64; decide) hi

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

end

end

/-!
# SEED-OFB and SEED-CFB128 on x86 (32-bit) meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86.ofb_wp`, `cfbEnc_wp`, and `cfbDecLevels_wp`, which deciphers
the blocks in groups) over SEED's core in the
encryption direction (`dirCoreSpec .encrypt`), with the working space as a
fifth argument (`fbX86`). The chaining value is written back, so it is
writable, and the taint analysis knows the argument words holding the
addresses of the data, the chaining value and the scratch buffer as the base
addresses of the writable regions. The `_framed` theorems run them with
their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.Impl.Seed.X86

theorem disjoint_empty (r : Region) (a : Addr) : Region.Disjoint ⟨a, 0⟩ r := fun _ h => by
  simp only [Region.Contains] at h; omega

theorem scr_eq (s : State) (d : Spec.Seed.Direction) :
    Modes.X86.scrR s (dirCore d) = ⟨(arg s 4).setWidth 64, 8 * 143⟩ := by
  simp [Modes.X86.scrR, dirCore, coreSlots, bufSlot, modeWs]

/-- The core's 20 bytes of stack, as the contracts write them. -/
theorem stk20_eq {s : State} (h : 20 ≤ (s.gpr .esp).toNat) :
    Proof.Modes.X86.stkRegion (s.gpr .esp) 20 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩ := by
  show (⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth h]

/-- The stack below the return address is apart from it. -/
theorem stk_ret (s : State) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨(s.gpr .esp).setWidth 64, 4⟩ :=
  (VG.Offset.base_disjoint_below _ (by decide)).symm

/-- The modes' slots are in the scratch buffer. -/
theorem modeSlots_sub (S : BitVec 32) (d : Spec.Seed.Direction) :
    Region.Sub ⟨Proof.Modes.X86.slotA S (dirCore d).slots, 40⟩ ⟨S.setWidth 64, 8 * 143⟩ :=
  VG.Offset.sub_base _ (by simp only [dirCore, coreSlots, bufSlot, modeWs]; omega_using [])

/-- The words of the first `n` stack arguments, readable, in `rd`. -/
theorem args_in {s : State} {n : Nat} {rd : List Region} (hfit : (s.gpr .esp).toNat + 4 * (n + 1) ≤ 2 ^ 32)
    (hrd : (⟨argAddr s 0, 4 * n⟩ : Region) ∈ rd) {i : Nat} (hi : i < n) :
    InRegions (rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.argOp i)) 4 ∧
      Region.Sub ⟨s.ea (VG.Impl.Aes.X86.argOp i), 4⟩ ⟨argAddr s 0, 4 * n⟩ := by
  rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, Proof.Modes.X86.argAddr_eq s (n := n) hfit hi]
  exact ⟨⟨_, List.mem_append_left _ hrd, VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hfit, hi])⟩,
    VG.Offset.sub_base _ (by omega_using [hi])⟩

end VG.Proof.Seed.X86

namespace VG.Proof.Seed.X86.Fb

open VG VG.X86 VG.Impl.Seed.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre ofb_wp cfbEnc_wp cfbDecLevels_wp)
open VG.Proof.Seed.X86 (scr_eq disjoint_empty KeyArgs dirCoreSpec)

/-- SEED under the schedule at the first argument. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 1).setWidth 64) 16
/-- The data. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m ((arg s 2).setWidth 64) (arg s 3).toNat

/-- The functions' postconditions. -/
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- OFB or CFB128 on x86 with its working space as the fifth argument, and
the postcondition `post`. -/
def fbX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 143⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 143 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ sched.Disjoint data ∧ sched.Disjoint iv ∧
    stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧
    20 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Spec.Seed.Direction) (hstep : M.step = 16)
    {s : State} (h : (fbX86 post).pre s) : SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, dKD, dKV, sK, sD, sV, sS,
    sA, sE⟩ := h
  have hL := (dirCoreSpec d).layout
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, coreSlots, bufSlot, modeWs]),
      (by simp only [dirCore, coreSlots, bufSlot, modeWs]; omega)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp [dirCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), ?_, ?_, ?_, ?_, sE, (by rw [hstep]; simp [dirCore]), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dRV
  · rw [show (dirCore d).stack = 20 from rfl, stk20_eq sE, hstep]; exact sD
  · rw [show (dirCore d).stack = 20 from rfl, stk20_eq sE]; exact sS.sub_right (modeSlots_sub _ d)
  · rw [show (dirCore d).stack = 20 from rfl, stk20_eq sE]; exact sA
  · rw [show (dirCore d).stack = 20 from rfl, stk20_eq sE]; exact stk_ret s

theorem keyArgs_of {post : State → State → Prop} (d : Spec.Seed.Direction) {s : State} (h : (fbX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore d)] (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, hwr, dKS, -, -, -, dAD, dAV, dAS, -, -, -, fK, -, -, -, fE, dKD, dKV, sK, -, -, sS, sA, sE⟩ := h
  have hA : (⟨argAddr s 0, 4 * 5⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain ⟨in0, sub0⟩ := args_in (n := 5) fE hA (i := 0) (by decide)
  obtain ⟨in4, sub4⟩ := args_in (n := 5) fE hA (i := 4) (by decide)
  have hrw : s.rd ++ s.wr = s.rd ++ s.wr := rfl
  rw [← stk20_eq sE] at sK sS sA
  have wD : ∀ {R : Region}, Region.Sub R ⟨argAddr s 0, 20⟩ → ∀ r ∈ s.wr, Region.Disjoint R r := fun hR r hr => by
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dAD.sub_left hR
    · exact dAV.sub_left hR
    · exact dAS.sub_left hR
  refine ⟨⟨arg s 0, in0, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_, wD sub0, sK, sA.sub_right sub0⟩,
    arg s 4, ⟨in4, rfl, wD sub4, sA.sub_right sub4⟩, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dKD
    · exact dKV
    · exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq, hwr]; simp
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact sS

theorem dirCore_ka (d : Spec.Seed.Direction) : (dirCore d).ka = 1 := rfl

theorem data_eq (d : Spec.Seed.Direction) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (dirCore d).bw) m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s := rfl
theorem iv_eq (d : Spec.Seed.Direction) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 1).setWidth 64) (4 * (dirCore d).bw) = ivAt m s := rfl
attribute [local irreducible] Spec.Seed.cipher in
theorem cipher_eq (s : State) :
    (dirCoreSpec .encrypt).cipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) = ciph s := rfl

theorem ofb_wp_x86 {s₀ : State} (hp : (fbX86 ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 ofbPost).post s₀ s' :=
  WP.mono (ofb_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : (fbX86 cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cfbDecPost).post s₀ s' :=
  WP.mono (cfbDecLevels_wp (dirCoreSpec .encrypt) (by decide) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions. -/
def fbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16, 8 * 143], argLen := 24,
    argBases := [(12, 0), (8, 1), (20, 2)], room := 20 }

theorem fbTaint_wf {post : State → State → Prop} {s : State} (hp : (fbX86 post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, dKD, dKV, sK, sD, sV,
    sS, sA, sE⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_using [fE], ?_⟩, ?_⟩ fun _ => ⟨sE, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [fE]) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [fE]) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [fE]) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact sD
    · exact sV
    · exact sS

theorem fbTaint_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (fbX86 post).pre s₁)
    (h₂ : (fbX86 post).pre s₂) (hpub : (fbX86 post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_using []), ha 2 (by omega_using []), ha 3 (by omega_using []), ha 4 (by omega_using [])]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem ofb_ct : ConstantTime isa (fbX86 ofbPost).pre (fbX86 ofbPost).pub ofb :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa (fbX86 cfbEncPost).pre (fbX86 cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 cfbDecPost).pre (fbX86 cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { fbX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 143⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 143 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ sched.Disjoint data ∧ sched.Disjoint iv ∧
      stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧
      20 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 16⟩, ⟨(arg s 4).setWidth 64, 8 * 143⟩]

tactic_template "narrow_seed_x86_fbverified" : tactic => `(tactic| simp only [VG.Proof.Seed.X86.Fb.fbX86, VG.Proof.Seed.X86.Fb.wideContract,
                     VG.Proof.Seed.X86.Fb.narrowRd, VG.Proof.Seed.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])
tactic_template "narrow_seed_x86_fbverified" loc:Lean.Parser.Tactic.location : tactic => `(tactic| simp only [VG.Proof.Seed.X86.Fb.fbX86, VG.Proof.Seed.X86.Fb.wideContract,
                     VG.Proof.Seed.X86.Fb.narrowRd, VG.Proof.Seed.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (fbX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow_seed_x86_fbverified
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 1144⟩, ⟨0x8004, 20⟩]

theorem wide_implies_ofb :
    (wideContract ofbPost).Implies (Proof.Seed.fbScratchContract X86.abi 143 Proof.Seed.ofbPost 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost] at h
    sig_split h
    sig_reduce [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
  · sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbEnc :
    (wideContract cfbEncPost).Implies (Proof.Seed.fbScratchContract X86.abi 143 Proof.Seed.cfbEncPost 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost] at h
    sig_split h
    sig_reduce [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
  · sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract cfbDecPost).Implies (Proof.Seed.fbScratchContract X86.abi 143 Proof.Seed.cfbDecPost 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost] at h
    sig_split h
    sig_reduce [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
  · sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
the chaining value at `0x2000`, and no blocks at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem frameSat_pre (post : Spec.Seed.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Seed.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1188)).pre s := by
  implies_sat [Spec.Seed.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem fb_verified {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (fbX86 post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (fbX86 post).post s s')
    (hct : ConstantTime isa (fbX86 post).pre (fbX86 post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (fbX86 post).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre post s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd narrowWr (wide_pre post) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    exact hR _ _ _ _ _ _ h
  · intro s₁ s₂ _ _ h
    narrow_seed_x86_fbverified
    exact h

theorem ofb_verified : Verified X86.target ofb (Proof.Seed.fbScratchContract X86.abi 143 Proof.Seed.ofbPost 20) :=
  fb_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb

theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt (Proof.Seed.fbScratchContract X86.abi 143 Proof.Seed.cfbEncPost 20) :=
  fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbEnc

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.Seed.fbScratchContract X86.abi 143 Proof.Seed.cfbDecPost 20) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 ofb)
      (Spec.Seed.ofbContract X86.abi 1188) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.ofbSig) (nm := "scratch") (e := .u64)
    (n := 143) (post := Proof.Seed.ofbPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1168) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.ofbPost_local _) (Proof.Seed.ofbPostOut_local _) (frameSat_pre _)

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 cfbEncrypt)
      (Spec.Seed.cfbEncryptContract X86.abi 1188) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 143) (post := Proof.Seed.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1168) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cfbEncPost_local _) (Proof.Seed.cfbEncPostOut_local _) (frameSat_pre _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 cfbDecrypt)
      (Spec.Seed.cfbDecryptContract X86.abi 1188) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 143) (post := Proof.Seed.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1168) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cfbDecPost_local _) (Proof.Seed.cfbDecPostOut_local _) (frameSat_pre _)

end VG.Proof.Seed.X86.Fb
