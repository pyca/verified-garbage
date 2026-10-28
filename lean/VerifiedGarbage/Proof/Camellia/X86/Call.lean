module

import VerifiedGarbage.Proof.Camellia.X86.PreparedVerified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Camellia.X86.Prologue
public import VerifiedGarbage.Proof.Camellia.X86.PreparedBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# Calls of Camellia's batches on x86 (32-bit)

`cryptCall_wp`: `cryptCall` (`Impl/Camellia/X86/Prepared.lean`), which ECB
(`Group.lean`) and the modes (`ModeCore.lean`) run on their scratch buffer,
calls `vg_camellia_crypt_prepared` (`WP.callWith`, with its contract on x86,
`cryptX86`) in a frame of its arguments, below the stack pointer and apart
from the scratch buffer: when the table of subkeys in the order of a
direction for 18 or 24 rounds is in the scratch buffer (`EntryOk`) and the
number of rounds in the caller's second stack argument, the eight blocks of
the tail buffer are ECB's in that direction, the callee-saved registers are
kept, and so is every byte of the working space but those of
`layout.cryptScratch` (`Keeps`), the table, ECB's saved registers and its
data pointer and count among them.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (argOp sb movR movI)

/-- A byte of the scratch buffer is outside the stack the call uses. -/
theorem byte_below {m m' : Mem} {E B : BitVec 32} {n o : Nat} {rs : List Region}
    (hf : Frame (rs ++ [below E 16]) m m') (hrs : ∀ r ∈ rs, Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 o, 1⟩ r)
    (hst : Region.Disjoint (below E 16) ⟨B.setWidth 64, n⟩) (hfit : B.toNat + n ≤ 2 ^ 32) (ho : o < n) :
    m' (B.setWidth 64 + BitVec.ofNat 64 o) = m (B.setWidth 64 + BitVec.ofNat 64 o) := by
  refine hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hrs r hr _ (Region.contains_self _ _) hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact hst _ hc (VG.Offset.contains_base _ (by omega) (by
      have := setWidth_toNat B; omega))

/-- A word of the scratch buffer from the table to the group's end, which
`vg_camellia_crypt_prepared` keeps. -/
theorem keeps_word {m m' : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32)
    (hk : Spec.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch m m') {k : Nat}
    (h1 : keySlot ≤ k) (h2 : k < grpSlot) : m'.readW (wordAddr B k) 32 = m.readW (wordAddr B k) 32 := by
  rw [keySlot_eq] at h1
  rw [grpSlot_eq] at h2
  rw [slots_eq] at hfit
  rw [slot_addr (by omega)]
  refine Mem.readW_congr fun i hi => ?_
  rw [VG.Offset.add_add]
  refine hk (4 * k + i) (by simp only [wsWords, slots_eq]; omega) fun r hr => ?_
  simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [keySlot_eq]; omega
  · simp only [grpSlot_eq]; omega

theorem cryptCall_wp {d : Dir} {s : State} {B : BitVec 32} {R : Nat} {ws : List (BitVec 64)}
    (hB : s.gpr sb = B) (hw : ScrIn s.wr B) (hR : R = 18 ∨ R = 24)
    (he : ∀ i < 8 * (R / 6) + 2, EntryOk s.mem B i (ws.getD (permOf d (R / 6) i) 0))
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4) (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (hst : Region.Disjoint (below (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * slots⟩)
    (hesp : 16 ≤ (s.gpr .esp).toNat) :
    WP isa cryptCall s fun s' => s'.gpr sb = B ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨B.setWidth 64, 4 * slots⟩, below (s.gpr .esp) 16] s.mem s'.mem ∧
      Spec.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch s.mem s'.mem ∧
      ∀ j < 8, Spec.Camellia.blockAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
        Proof.Camellia.blockFn (Spec.Camellia.subkeysOfWords R ws) (specDir d)
          (Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j))) := by
  have hfit' : B.toNat + 4 * slots ≤ 2 ^ 32 := hw.fit
  obtain ⟨N, hN, -, hNw⟩ := hw.mem
  have hH : Spec.Camellia.Prepared.Holds layout s.mem (B.setWidth 64) R ws (specDir d) :=
    holds_of_words hfit' hR (words_of_entries fun e he' => by rw [ofSpecDir_specDir, keyEntry_eq]; exact he e he')
  -- The arguments.
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 1 ha
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := movR_ok s₁ .ecx sb
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .edx (BitVec.ofNat 32 wsWords)
  have g₃ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₃ r h3, o₂ r h2, o₁ r h1]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := g₃ _ (by decide) (by decide) (by decide)
  have eax₃ : s₃.gpr .eax = BitVec.ofNat 32 R := by
    rw [o₃ _ (by decide), o₂ _ (by decide), v₁]; exact hv
  have ecx₃ : s₃.gpr .ecx = B := by rw [o₃ _ (by decide), v₂, o₁ _ (by decide), hB]
  have mem₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  unfold cryptCall
  refine WP.seq (WP.of_runBlock ⟨s₃, ?_, ?_⟩)
  · rw [show ([.mov .eax (.mem (argOp 1)), movR .ecx sb, movI .edx (BitVec.ofNat 32 wsWords)] : List Instr) =
      [.mov .eax (.mem (argOp 1))] ++ ([movR .ecx sb] ++ [movI .edx (BitVec.ofNat 32 wsWords)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  -- The call.
  have hrs : Reg.esp ∉ [Reg.edx, .ecx, .eax] := by decide
  have hfit₃ : 4 * [Reg.edx, .ecx, .eax].length + 4 ≤ (s₃.gpr .esp).toNat := by
    rw [esp₃]; show 16 ≤ _; omega
  have a0 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 0 = BitVec.ofNat 32 R := by
    rw [callEntry_arg hfit₃ hrs (i := 0) (by decide)]; exact eax₃
  have a1 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 1 = B := by
    rw [callEntry_arg hfit₃ hrs (i := 1) (by decide)]; exact ecx₃
  have a2 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 2 = BitVec.ofNat 32 wsWords := by
    rw [callEntry_arg hfit₃ hrs (i := 2) (by decide)]; exact v₃
  have cE := callEntry_frame hfit₃ hrs
  rw [show 4 * [Reg.edx, .ecx, .eax].length + 4 = 16 from rfl, esp₃, mem₃] at cE
  have cE' : Frame ([] ++ [below (s.gpr .esp) 16]) s.mem (pushed [.edx, .ecx, .eax] s₃).callEntry.mem := cE
  have hHC : Spec.Camellia.Prepared.Holds layout (pushed [.edx, .ecx, .eax] s₃).callEntry.mem (B.setWidth 64) R ws
      (specDir d) := fun r hr i hi => by
    have hg : R / 6 ≤ 4 := by omega
    have hr' := hr
    rw [layout_table] at hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    dsimp only at hi ⊢
    rw [byte_below cE' (fun _ h => (List.not_mem_nil h).elim) hst hfit' (by rw [slots_eq]; omega)]
    exact hH _ hr i hi
  have wsN : (BitVec.ofNat 32 wsWords).toNat = 336 := rfl
  have argsC : argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 12).setWidth 64 := by
    rw [callEntry_argAddr0, esp₃]; rfl
  have espC : ((pushed [.edx, .ecx, .eax] s₃).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 16 := by
    rw [callEntry_espNat hfit₃, esp₃]; rfl
  have espC' : ((pushed [.edx, .ecx, .eax] s₃).callEntry.gpr .esp).setWidth 64 =
      (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_esp', esp₃]; rfl
  have argsSub : Region.Sub ⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩ (below (s.gpr .esp) 16) := by
    rw [argsC]; exact below_sub (by omega) hesp
  have hst2 : Region.Disjoint (below (s.gpr .esp) 16) ⟨B.setWidth 64, 336 * 8⟩ := by
    have := hst; rw [slots_eq] at this; exact this
  have hR32 : R < 2 ^ 32 := by omega
  have scrIn : (⟨B.setWidth 64, 4 * N⟩ : Region) ∈ s₃.wr := by rw [wr₃']; exact hNw
  refine WP.callWith (k := cryptX86) crypt_correct crypt_noSp (by decide) hrs
    (by rw [crypt_stackUse, esp₃]; show 16 ≤ _; omega)
    (rd := [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]) (wr := [⟨B.setWidth 64, 336 * 8⟩])
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ fun s' rd' wr' cs f ⟨s₂, m₂, post⟩ => ?_
  · rw [State.withRegions_rd, argAddr_withRegions]
  · rw [State.withRegions_wr, arg_withRegions, arg_withRegions, a1, a2]; rfl
  · rw [argAddr_withRegions, arg_withRegions, arg_withRegions, a1, a2]
    exact (hst2.sub_left argsSub)
  · rw [State.withRegions_gpr, arg_withRegions, arg_withRegions, a1, a2, espC']
    exact (hst2.sub_left (Region.sub_prefix (by decide)))
  · rw [arg_withRegions, arg_withRegions, a1, a2, wsN]; rw [slots_eq] at hfit'; omega
  · rw [State.withRegions_gpr, espC]; have := (s.gpr .esp).isLt; omega
  · rw [arg_withRegions, a0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32]; exact hR
  · rw [arg_withRegions, a2, wsN, size_eq, slots_eq]
  · refine ⟨ws, specDir d, ?_⟩
    rw [arg_withRegions, arg_withRegions, a0, a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32, State.withRegions_mem]
    exact hHC
  · refine Covers.append_left (Covers.right (Covers.of_mem fun r hr => ?_)) (Covers.right ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [argsC, ← esp₃]; exact List.mem_cons_self
    · exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ scrIn, 0, by rw [BitVec.add_zero],
          by show 0 + 336 * 8 ≤ 4 * N; rw [slots_eq] at hN; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ scrIn, 0, by rw [BitVec.add_zero],
      by show 0 + 336 * 8 ≤ 4 * N; rw [slots_eq] at hN; omega⟩
  -- After the call.
  have hHC' : Spec.Camellia.Prepared.Holds layout
      ((pushed [.edx, .ecx, .eax] s₃).callEntry.withRegions [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]
        [⟨B.setWidth 64, 336 * 8⟩]).mem
      ((arg ((pushed [.edx, .ecx, .eax] s₃).callEntry.withRegions [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]
        [⟨B.setWidth 64, 336 * 8⟩]) 1).setWidth 64)
      (arg ((pushed [.edx, .ecx, .eax] s₃).callEntry.withRegions [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]
        [⟨B.setWidth 64, 336 * 8⟩]) 0).toNat ws (specDir d) := by
    rw [arg_withRegions, arg_withRegions, a0, a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32, State.withRegions_mem]
    exact hHC
  have hE := post.1 ws (specDir d) hHC'
  have hK := post.2
  simp only [arg_withRegions, a0, a1, a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR32, State.withRegions_mem,
    m₂] at hE hK
  rw [show wsWords % 2 ^ 32 = wsWords from rfl] at hK
  have fS : Frame [⟨B.setWidth 64, 4 * slots⟩, below (s.gpr .esp) 16] s.mem s'.mem := by
    rw [← mem₃]
    refine f.sub fun r hr => ?_
    rw [crypt_stackUse] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [slots_eq]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by rw [esp₃]; exact fun _ h => h⟩
  -- The bytes of the frame, outside the call's.
  have hK' : Spec.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch s.mem s'.mem :=
    fun i hi hout => by
      rw [hK i hi hout]
      exact byte_below cE' (fun _ h => (List.not_mem_nil h).elim) hst2 (by rw [slots_eq] at hfit'; omega)
        (by simp only [wsWords, slots_eq] at hi; omega)
  refine ⟨by rw [show sb = .edi from rfl, cs .edi (by decide), g₃ _ (by decide) (by decide) (by decide)]; exact hB,
    fun r hr => by rw [cs r hr, g₃ r (fun h => by subst h; simp [calleeSaved] at hr)
      (fun h => by subst h; simp [calleeSaved] at hr) (fun h => by subst h; simp [calleeSaved] at hr)],
    by rw [rd', rd₃'], by rw [wr', wr₃'], fS, hK', fun j hj => ?_⟩
  have hb := congrArg (fun l => l[j]?) hE
  rw [Proof.Camellia.ecb_eq] at hb
  simp only [Spec.Camellia.blocksAt, layout, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at hb
  have hblk : ∀ (m : Mem), Frame ([] ++ [below (s.gpr .esp) 16]) s.mem m →
      Spec.Camellia.blockAt m (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) + BitVec.ofNat 64 (16 * j)) =
      Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) + BitVec.ofNat 64 (16 * j)) :=
    fun m hm => by
      apply Vector.ext; intro i hi
      simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn, VG.Offset.add_add]
      exact byte_below hm (fun _ h => (List.not_mem_nil h).elim) hst hfit'
        (by rw [slots_eq, tailSlot_eq]; omega)
  rw [← VG.Offset.add_add, hb, hblk _ cE']

end VG.Proof.Camellia.X86
