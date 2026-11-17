module

public import VerifiedGarbage.Proof.Camellia.X86.Prologue
public import VerifiedGarbage.Proof.Camellia.X86.PreparedBody
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Camellia.X86.Copy
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Camellia.X86.PreparedVerified
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-! ### `Camellia.X86.Call`, which this module and modules that import it used -/

section

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
    exact hst _ hc (VG.Offset.contains_base _ (by omega_using [ho]) (by
      have := setWidth_toNat B; omega_using [hfit, ho]))

/-- A word of the scratch buffer from the table to the group's end, which
`vg_camellia_crypt_prepared` keeps. -/
theorem keeps_word {m m' : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32)
    (hk : Proof.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch m m') {k : Nat}
    (h1 : keySlot ≤ k) (h2 : k < grpSlot) : m'.readW (wordAddr B k) 32 = m.readW (wordAddr B k) 32 := by
  rw [keySlot_eq] at h1
  rw [grpSlot_eq] at h2
  rw [slots_eq] at hfit
  rw [slot_addr (by omega_using [hfit, h2])]
  refine Mem.readW_congr fun i hi => ?_
  rw [VG.Offset.add_add]
  refine hk (4 * k + i) (by simp only [wsWords, slots_eq]; omega_using [h2, hi]) fun r hr => ?_
  simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [keySlot_eq]; omega_using [h1]
  · simp only [grpSlot_eq]; omega_using [h2, hi]

theorem cryptCall_wp {d : Dir} {s : State} {B : BitVec 32} {R : Nat} {ws : List (BitVec 64)}
    (hB : s.gpr sb = B) (hw : ScrIn s.wr B) (hR : R = 18 ∨ R = 24)
    (he : ∀ i < 8 * (R / 6) + 2, EntryOk s.mem B i (ws.getD (permOf d (R / 6) i) 0))
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4) (hv : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R)
    (hst : Region.Disjoint (below (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * slots⟩)
    (hesp : 16 ≤ (s.gpr .esp).toNat) :
    WP isa cryptCall s fun s' => s'.gpr sb = B ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨B.setWidth 64, 4 * slots⟩, below (s.gpr .esp) 16] s.mem s'.mem ∧
      Proof.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch s.mem s'.mem ∧
      ∀ j < 8, Spec.Camellia.blockAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
        Proof.Camellia.blockFn (Spec.Camellia.subkeysOfWords R ws) (specDir d)
          (Spec.Camellia.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j))) := by
  have hfit' : B.toNat + 4 * slots ≤ 2 ^ 32 := hw.fit
  obtain ⟨N, hN, -, hNw⟩ := hw.mem
  have hH : Proof.Camellia.Prepared.Holds layout s.mem (B.setWidth 64) R ws (specDir d) :=
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
    rw [esp₃]; show 16 ≤ _; omega_using [hesp]
  have a0 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 0 = BitVec.ofNat 32 R := by
    rw [callEntry_arg hfit₃ hrs (i := 0) (by decide)]; exact eax₃
  have a1 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 1 = B := by
    rw [callEntry_arg hfit₃ hrs (i := 1) (by decide)]; exact ecx₃
  have a2 : arg (pushed [.edx, .ecx, .eax] s₃).callEntry 2 = BitVec.ofNat 32 wsWords := by
    rw [callEntry_arg hfit₃ hrs (i := 2) (by decide)]; exact v₃
  have cE := callEntry_frame hfit₃ hrs
  rw [show 4 * [Reg.edx, .ecx, .eax].length + 4 = 16 from rfl, esp₃, mem₃] at cE
  have cE' : Frame ([] ++ [below (s.gpr .esp) 16]) s.mem (pushed [.edx, .ecx, .eax] s₃).callEntry.mem := cE
  have hHC : Proof.Camellia.Prepared.Holds layout (pushed [.edx, .ecx, .eax] s₃).callEntry.mem (B.setWidth 64) R ws
      (specDir d) := fun r hr i hi => by
    have hg : R / 6 ≤ 4 := by omega_using [hR]
    have hr' := hr
    rw [layout_table] at hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    dsimp only at hi ⊢
    rw [byte_below cE' (fun _ h => (List.not_mem_nil h).elim) hst hfit' (by rw [slots_eq]; omega_using [hR, hi])]
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
    rw [argsC]; exact below_sub (by omega_using []) hesp
  have hst2 : Region.Disjoint (below (s.gpr .esp) 16) ⟨B.setWidth 64, 336 * 8⟩ := by
    have := hst; rw [slots_eq] at this; exact this
  have hR32 : R < 2 ^ 32 := by omega_using [hR]
  have scrIn : (⟨B.setWidth 64, 4 * N⟩ : Region) ∈ s₃.wr := by rw [wr₃']; exact hNw
  refine WP.callWith (k := cryptX86) crypt_correct crypt_noSp (by decide) hrs
    (by rw [crypt_stackUse, esp₃]; show 16 ≤ _; omega_using [hesp])
    (rd := [⟨argAddr (pushed [.edx, .ecx, .eax] s₃).callEntry 0, 12⟩]) (wr := [⟨B.setWidth 64, 336 * 8⟩])
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ fun s' rd' wr' cs f ⟨s₂, m₂, post⟩ => ?_
  · rw [State.withRegions_rd, argAddr_withRegions]
  · rw [State.withRegions_wr, arg_withRegions, arg_withRegions, a1, a2]; rfl
  · rw [argAddr_withRegions, arg_withRegions, arg_withRegions, a1, a2]
    exact (hst2.sub_left argsSub)
  · rw [State.withRegions_gpr, arg_withRegions, arg_withRegions, a1, a2, espC']
    exact (hst2.sub_left (Region.sub_prefix (by decide)))
  · rw [arg_withRegions, arg_withRegions, a1, a2, wsN]; rw [slots_eq] at hfit'; omega_using [hfit']
  · rw [State.withRegions_gpr, espC]; have := (s.gpr .esp).isLt; omega_using []
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
          by show 0 + 336 * 8 ≤ 4 * N; rw [slots_eq] at hN; omega_using [hN]⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ scrIn, 0, by rw [BitVec.add_zero],
      by show 0 + 336 * 8 ≤ 4 * N; rw [slots_eq] at hN; omega_using [hN]⟩
  -- After the call.
  have hHC' : Proof.Camellia.Prepared.Holds layout
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
  have hK' : Proof.Camellia.Prepared.Keeps (B.setWidth 64) wsWords layout.cryptScratch s.mem s'.mem :=
    fun i hi hout => by
      rw [hK i hi hout]
      exact byte_below cE' (fun _ h => (List.not_mem_nil h).elim) hst2 (by rw [slots_eq] at hfit'; omega_using [hfit'])
        (by simp only [wsWords, slots_eq] at hi; omega_using [hi])
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
        (by rw [slots_eq, tailSlot_eq]; omega_using [hj, hi])
  rw [← VG.Offset.add_add, hb, hblk _ cE']

end VG.Proof.Camellia.X86

end

end

/-! ### `Camellia.X86.Group`, which only this module used -/

section

/-!
# A group of blocks of Camellia ECB on x86 (32-bit)

As SM4's (`Proof/Sm4/X86/Ecb.lean`, whose code is the same but for the
rounds): `dataGroup_wp`, one iteration of the data loop, copies the group's
blocks (eight, or the last one to seven) to the tail buffer, transforms it
by a call of `vg_camellia_crypt_prepared` (`cryptCall_wp`), with the number
of rounds in ECB's second stack argument and its frame below the stack
pointer, copies the blocks back and steps to the next group. The data
pointer and the blocks left live in their slots (`dSlot`, `nSlot`) between
the steps, which the call keeps, as it keeps the table and the saved
registers (`ScrOk.keeps`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Proof.Camellia (DInv outF not_contains_off blockAt_getD)
open VG.Impl.Aes.X86 (sb slotAt movS st movR addI subI subR movI)

/-! ## Small blocks -/

/-- `ecx := min(ebp, 8)`. -/
theorem countR_wp {s : State} {v : Nat} (hn : s.gpr .ebp = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa countR s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .ecx .ebp
  let s₂ := arithFlags s₁ (s₁.gpr .ebp - 8) ((s₁.gpr .ebp).toNat < (8 : BitVec 32).toNat)
    (subOverflow (s₁.gpr .ebp) 8 (s₁.gpr .ebp - 8))
  obtain e₂ : runBlock isa [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] s = some s₂ := by
    rw [show ([movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] : List Instr) =
      [movR .ecx .ebp] ++ [.alu .cmp .ebp (.imm 8)] from rfl, runBlock_app, e₁, Option.bind_some]
    rfl
  obtain ebp₂ : s₂.gpr .ebp = BitVec.ofNat 32 v := by rw [RegUpd.gpr_arithFlags, o₁ _ (by decide), hn]
  obtain cf₂ : s₂.cf = some (decide (v < 8)) := by
    rw [RegUpd.cf_arithFlags, o₁ _ (by decide), hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl
  obtain o₂ : ∀ r, r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr]
  obtain m₂ : s₂.mem = s.mem := by rw [RegUpd.mem_arithFlags, m₁]
  obtain rd₂ : s₂.rd = s.rd := by rw [RegUpd.rd_arithFlags, rd₁]
  obtain wr₂ : s₂.wr = s.wr := by rw [RegUpd.wr_arithFlags, wr₁]
  unfold countR
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.ite (decide (v < 8)) ((eval_b s₂).trans cf₂) (fun h => ?_) (fun h => ?_)
  · refine WP.block_nil ⟨?_, o₂, m₂, rd₂, wr₂⟩
    rw [RegUpd.gpr_arithFlags, r₁, hn, Nat.min_eq_left (by simp at h; omega_arith)]
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .ecx 8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => by rw [o₃ r hr, o₂ r hr], by rw [m₃, m₂],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    rw [r₃, Nat.min_eq_right (by simp at h; omega_arith)]; rfl

/-- The data pointer and the blocks left from their slots to `esi` and
`ebp`, and `ecx := min(ebp, 8)`. -/
theorem groupCount_wp {s : State} {b A : BitVec 32} {v : Nat} (hb : s.gpr .edi = b) (hw : ScrIn s.wr b)
    (hd : s.mem.readW (wordAddr b dSlot) 32 = A) (hn : s.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v)
    (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .esi = A ∧ s'.gpr .ebp = BitVec.ofNat 32 v ∧
      s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .esi .edi (k := dSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok s₁ .ebp .edi (k := nSlot)
    (by rw [o₁ _ (by decide), hb]) (by decide) (by rw [wr₁]; exact hw)
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (countR_wp (by rw [r₂, m₁, hn]) hv)
    fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_⟩)
  · rw [show ([movS .esi dSlot, movS .ebp nSlot] : List Instr) =
      [.mov .esi (.mem (slotAt .edi dSlot))] ++ [.mov .ebp (.mem (slotAt .edi nSlot))] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · exact ⟨by rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hd], by rw [o₃ _ (by decide), r₂, m₁, hn], c₃,
      fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩

/-- `st dSlot, esi; st nSlot, ebp`. -/
theorem stDN_ok (s : State) {b : BitVec 32} (hb : s.gpr .edi = b) (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [st dSlot .esi, st nSlot .ebp] s = some s' ∧
      s'.mem.readW (wordAddr b dSlot) 32 = s.gpr .esi ∧ s'.mem.readW (wordAddr b nSlot) 32 = s.gpr .ebp ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩] s.mem s'.mem := by
  have hfit : b.toNat + 4 * slots ≤ 2 ^ 32 := hw.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, z₁, -, f₁⟩ := stSlot_ok s .esi .edi (k := dSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, z₂, -, f₂⟩ := stSlot_ok s₁ .ebp .edi (k := nSlot) (by rw [g₁, hb])
    (by decide) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, ?_, ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [z₂, z₁],
    (f₁.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
  · rw [show ([st dSlot .esi, st nSlot .ebp] : List Instr) =
      [.store (slotAt .edi dSlot) .esi] ++ [.store (slotAt .edi nSlot) .ebp] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  · rw [m₂, readW_slot_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₁,
      readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl]
  · rw [m₂, readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₁]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem setWidth_add {D : BitVec 32} {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-! ## The scratch buffer's contents -/

/-- What the data loop keeps in the scratch buffer: the table of `8 g + 2`
subkeys and the saved registers, in the slots from `keySlot` to `dSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  hg : g = 3 ∨ g = 4
  keys : ∀ i < 8 * g + 2, W32.HalfRel (entryW m b i) fun _ => E i
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b keySlot dSlot).Disjoint r) : ScrOk s₀ b g E m' := by
  obtain hg4 : 8 * g + 2 ≤ 34 := by rcases h.hg with h | h <;> omega_arith
  refine ⟨h.hg, fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf hd (by omega_arith) (by rw [dSlot_eq, keySlot_eq]; omega_arith)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, keySlot_eq]; omega_arith)
      (by rw [savedSlot_eq, dSlot_eq]; omega_arith)

theorem ScrOk.keeps {s₀ : State} {b : BitVec 32} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    (hk : Proof.Camellia.Prepared.Keeps (b.setWidth 64) wsWords layout.cryptScratch m m') : ScrOk s₀ b g E m' := by
  obtain hg4 : 8 * g + 2 ≤ 34 := by rcases h.hg with h | h <;> omega_arith
  refine ⟨h.hg, fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact keeps_word hfit hk (by omega_arith) (by rw [grpSlot_eq, keySlot_eq]; omega_arith)
  · rw [← h.saved i hi]
    exact keeps_word hfit hk (by rw [savedSlot_eq, keySlot_eq]; omega_arith) (by rw [savedSlot_eq, grpSlot_eq]; omega_arith)

/-- The slots of the data pointer and the count are in the scratch buffer. -/
theorem dn_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      Region.Sub r ⟨b.setWidth 64, 4 * slots⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact slot_sub hfit (by decide)
  · exact slot_sub hfit (by decide)

/-- … and apart from the table and the saved registers. -/
theorem dn_disj {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b keySlot dSlot).Disjoint r := fun r hr => by
  rw [slots_eq] at hfit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
    exact VG.Offset.disjoint _ (by (try simp only [keySlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
      (by (try simp only [keySlot_eq, dSlot_eq]); omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)

/-! ## The data loop -/

/-- The registers the steps keep, which the call keeps too. -/
theorem mem_calleeSaved {r : Reg} (h1 : r ≠ .esi) (h2 : r ≠ .ebp) (h3 : r ≠ .ecx) (h4 : r ≠ .edx) (h5 : r ≠ .ebx)
    (h6 : r ≠ .eax) : r ∈ calleeSaved := by
  cases r <;> simp_all [calleeSaved]

/-- The scratch buffer at `b`, the `n` blocks at `D`, `R` rounds in the
second stack argument, and the 16 bytes of stack below the stack pointer
that the call uses, apart from the others. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n R : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ ⟨b.setWidth 64, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  rounds : R = 18 ∨ R = 24
  argIn : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ 1) 4
  argV : s₀.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 R
  argS : Region.Disjoint ⟨argAddr s₀ 1, 4⟩ ⟨b.setWidth 64, 4 * slots⟩
  argD : Region.Disjoint ⟨argAddr s₀ 1, 4⟩ ⟨D.setWidth 64, 16 * n⟩
  stkS : Region.Disjoint (below (s₀.gpr .esp) 16) ⟨b.setWidth 64, 4 * slots⟩
  stkD : Region.Disjoint (below (s₀.gpr .esp) 16) ⟨D.setWidth 64, 16 * n⟩
  stkA : Region.Disjoint (below (s₀.gpr .esp) 16) ⟨argAddr s₀ 1, 4⟩
  esp16 : 16 ≤ (s₀.gpr .esp).toNat

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) :
    Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  dp : s.mem.readW (wordAddr b dSlot) 32 = D + BitVec.ofNat 32 (128 * k)
  np : s.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n (8 * k) (outF s₀.mem (D.setWidth 64) g E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩, below (s₀.gpr .esp) 16] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) g E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩, below (s₀.gpr .esp) 16] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n R : Nat} {g : Nat} {E : Nat → BitVec 64} {dir : Dir}
    {ws : List (BitVec 64)} (hp : GPre s₀ b D n R) (hg : R / 6 = g) (hE : ∀ i, E i = ws.getD (permOf dir g i) 0)
    {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.X86.group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n g E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := setWidth_toNat b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : A.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (128 * k) := setWidth_add (by omega_arith)
  obtain hT : T.setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) :=
    setWidth_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (T.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    obtain ⟨N, hN, hNf, hNr⟩ := hwS.mem
    refine ⟨_, hNr, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq] at *; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (A.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨A.setWidth 64, 16 * c⟩ ⟨D.setWidth 64, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨T.setWidth 64, 16 * c⟩ ⟨b.setWidth 64, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨T.setWidth 64, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `keySlot`.
  obtain dT : (slotsRegion b keySlot grpSlot).Disjoint ⟨T.setWidth 64, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [keySlot_eq, tailSlot_eq]; omega_arith)
      (by rw [keySlot_eq, grpSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain dA : (slotsRegion b keySlot grpSlot).Disjoint ⟨A.setWidth 64, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [keySlot_eq, grpSlot_eq, slots_eq]; omega_arith))).symm
  obtain subTab : (slotsRegion b keySlot dSlot).Sub (slotsRegion b keySlot grpSlot) :=
    VG.Offset.sub _ (by decide) (by decide)
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain hsub := dn_sub hfit'
  obtain dsTab := dn_disj hfit'
  unfold Impl.Camellia.X86.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.base hwS hi.dp hi.np hv)
    fun s₁ ⟨esi₁, ebp₁, ecx₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, -, -⟩ := movR_ok s₁ .edx .esi
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b, -, -⟩ := movR_ok s₂a .ebx .edi
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₂b .ebx (BitVec.ofNat 32 (4 * tailSlot))
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [tailAddr, show ([movR .edx .esi] ++ [movR .ebx .edi, addI .ebx (BitVec.ofNat 32 (4 * tailSlot))] :
        List Instr) = [movR .edx .esi] ++ ([movR .ebx .edi] ++ [addI .ebx (BitVec.ofNat 32 (4 * tailSlot))])
        from rfl, runBlock_app, e₂a, Option.bind_some, runBlock_app, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, esi₁]; simp [A],
      by rw [r₂, r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂b _ (by decide), o₂a _ (by decide), ecx₁, Nat.sub_zero],
      ⟨fun t ht => by omega_arith, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ h₃ => ?_)
  obtain f₃ : Frame [⟨T.setWidth 64, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₃.gpr r = s₁.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₃.regs r h0 h1 h2 h3, o₂ r h1, o₂b r h1, o₂a r h0]
  obtain base₃ : s₃.gpr .edi = b := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b g E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left back to their slots.
  obtain ⟨s₄, e₄, dp₄, np₄, g₄, rd₄, wr₄, -, fs⟩ := stDN_ok s₃ base₃ hwS₃
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  obtain esi₃ : s₃.gpr .esi = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), esi₁]
  obtain ebp₃ : s₃.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), ebp₁]
  rw [esi₃] at dp₄
  rw [ebp₃] at np₄
  obtain sc₄ : ScrOk s₀ b g E s₄.mem := sc₃.frame hfit' fs dsTab
  obtain base₄ : s₄.gpr sb = b := by rw [g₄]; exact base₃
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃]
  -- The eight blocks, by the call.
  obtain esp₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [g₄, g₃ _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide) (by decide), hi.esp]
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, hi.rd]
  obtain fr₄ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩, below (s₀.gpr .esp) 16] s₀.mem s₄.mem :=
    hi.frame.trans ((f₃.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (fs.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩))
  obtain ha₄ : InRegions (s₄.rd ++ s₄.wr) (s₄.ea (VG.Impl.Aes.X86.argOp 1)) 4 := by
    rw [rd₄', wr₄', hi.wr, ea_arg esp₄]; exact hp.argIn
  obtain hv₄ : s₄.mem.readW (s₄.ea (VG.Impl.Aes.X86.argOp 1)) 32 = BitVec.ofNat 32 R := by
    rw [ea_arg esp₄, fr₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.argS
      · exact hp.argD
      · exact hp.stkA.symm) (by decide)]
    exact hp.argV
  obtain he₄ : ∀ i < 8 * (R / 6) + 2, EntryOk s₄.mem b i (ws.getD (permOf dir (R / 6) i) 0) := fun i hi' => by
    rw [hg] at hi' ⊢; rw [← hE]; exact sc₄.keys i hi'
  refine WP.seq (WP.mono (cryptCall_wp base₄ (by rw [wr₄']; exact hwS) hp.rounds he₄ ha₄ hv₄
    (by rw [esp₄]; exact hp.stkS) (by rw [esp₄]; exact hp.esp16))
    fun s₅ ⟨bb₅, cs₅, rd₅', wr₅', f₅, k₅, bl₅⟩ => ?_)
  have base₅ : s₅.gpr .edi = b := bb₅
  rw [esp₄] at f₅
  obtain keep₅ : ∀ j, keySlot ≤ j → j < grpSlot →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => keeps_word hfit' k₅ h1 h2
  obtain sc₅ : ScrOk s₀ b g E s₅.mem := sc₄.keeps hfit' k₅
  obtain b₅ : ∀ j < 8, blk s₅ j =
      Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₄ j))) := fun j hj => by
    obtain hEf : (fun i => ws.getD (Proof.Camellia.dirPerm (specDir dir) g i) 0) = E := funext fun i => (hE i).symm
    simp only [blk]
    rw [show s₅.gpr sb = b from base₅, base₄, bl₅ j hj, blockFn_words (specDir dir) hp.rounds, hg, hEf]
  obtain wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp (A := A) base₅ hwS₅
    (by rw [keep₅ _ (by decide) (by decide)]; exact dp₄) (by rw [keep₅ _ (by decide) (by decide)]; exact np₄) hv)
    fun s₆ ⟨esi₆, ebp₆, ecx₆, o₆, m₆, rd₆, wr₆⟩ => ?_))
  obtain ⟨s₇a, e₇a, r₇a, o₇a, m₇a, rd₇a, wr₇a, -, -⟩ := movR_ok s₆ .edx .edi
  obtain ⟨s₇b, e₇b, r₇b, -, o₇b, m₇b, rd₇b, wr₇b⟩ := addI_ok s₇a .edx (BitVec.ofNat 32 (4 * tailSlot))
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇, -, -⟩ := movR_ok s₇b .ebx .esi
  obtain mem₇ : s₇.mem = s₅.mem := by rw [m₇, m₇b, m₇a, m₆]
  obtain rd₇' : s₇.rd = s.rd := by rw [rd₇, rd₇b, rd₇a, rd₆, rd₅]
  obtain wr₇' : s₇.wr = s.wr := by rw [wr₇, wr₇b, wr₇a, wr₆, wr₅]
  refine WP.seq (WP.of_runBlock ⟨s₇, by
    rw [tailAddr, show ([movR .edx .edi, addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi] :
        List Instr) = [movR .edx .edi] ++ ([addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi])
        from rfl, runBlock_app, e₇a, Option.bind_some, runBlock_app, e₇b, Option.bind_some, e₇], ?_⟩)
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₇', wr₇']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₇']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₇ _ (by decide), r₇b, r₇a, o₆ _ (by decide) (by decide) (by decide), base₅]; simp [T],
      by rw [r₇, o₇b _ (by decide), o₇a _ (by decide), esi₆]; simp [A],
      by rw [o₇ _ (by decide), o₇b _ (by decide), o₇a _ (by decide), ecx₆, Nat.sub_zero],
      ⟨fun t ht => by omega_arith, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₈ h₈ => ?_
  obtain f₈ : Frame [⟨A.setWidth 64, 16 * c⟩] s₅.mem s₈.mem := by rw [← mem₇]; exact h₈.cp.frame
  obtain g₈ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₈.gpr r = s₆.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₈.regs r h0 h1 h2 h3, o₇ r h1, o₇b r h0, o₇a r h0]
  obtain sc₈ : ScrOk s₀ b g E s₈.mem := sc₅.frame hfit' f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  obtain wr₈ : s₈.wr = s.wr := by rw [h₈.wr, wr₇']
  obtain rd₈ : s₈.rd = s.rd := by rw [h₈.rd, rd₇']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, blk s₄ j =
      Spec.Camellia.blockAt s₀.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
        ¬ r.Contains (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₈.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D.setWidth 64 + BitVec.ofNat 64 i = A.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₈.cp.copied _ (by omega_arith), mem₇, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) =
          (s₅.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [show s₅.gpr sb = b from base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A.setWidth 64, 16 * c⟩ : Region)],
          ¬ r.Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hA]
        exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₈ _ hout,
        f₅.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.sep
          · exact hp.stkD.symm) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  -- On to the next group.
  obtain esi₈ : s₈.gpr .esi = A := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), esi₆]
  obtain ebp₈ : s₈.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  unfold advance
  refine WP.seq (WP.mono (countR_wp ebp₈ hv) fun s₉ ⟨ecx₉, o₉, m₉, rd₉, wr₉⟩ => ?_)
  obtain ⟨s₁₀a, e₁₀a, r₁₀a, -, o₁₀a, m₁₀a, rd₁₀a, wr₁₀a⟩ := addI_ok s₉ .esi 128
  obtain ⟨s₁₀b, e₁₀b, r₁₀b, z₁₀b, o₁₀b, m₁₀b, rd₁₀b, wr₁₀b⟩ := subI_ok s₁₀a .ebp (s₁₀a.gpr .ecx)
  obtain base₁₀b : s₁₀b.gpr .edi = b := by
    rw [o₁₀b _ (by decide), o₁₀a _ (by decide), o₉ _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide) (by decide), base₅]
  obtain wr₁₀b' : s₁₀b.wr = s.wr := by rw [wr₁₀b, wr₁₀a, wr₉, wr₈]
  obtain ⟨s₁₀, e₁₀, dp₁₀, np₁₀, g₁₀, rd₁₀, wr₁₀, z₁₀, fa⟩ := stDN_ok s₁₀b base₁₀b (by rw [wr₁₀b']; exact hwS)
  refine WP.of_runBlock ⟨s₁₀, by
    rw [show ([addI .esi 128, subR .ebp .ecx, st dSlot .esi, st nSlot .ebp] : List Instr) =
      [addI .esi 128] ++ ([subR .ebp .ecx] ++ [st dSlot .esi, st nSlot .ebp]) from rfl,
      runBlock_app, e₁₀a, Option.bind_some, runBlock_app,
      show runBlock isa [subR .ebp .ecx] s₁₀a = runBlock isa [subI .ebp (s₁₀a.gpr .ecx)] s₁₀a from rfl,
      e₁₀b, Option.bind_some, e₁₀], ?_⟩
  obtain ecx₁₀a : s₁₀a.gpr .ecx = BitVec.ofNat 32 c := by rw [o₁₀a _ (by decide), ecx₉]
  obtain ebp₁₀a : s₁₀a.gpr .ebp = BitVec.ofNat 32 v := by rw [o₁₀a _ (by decide), o₉ _ (by decide), ebp₈]
  obtain zz : s₁₀.zf = some (decide (v = c)) := by
    rw [z₁₀, z₁₀b, ebp₁₀a, ecx₁₀a, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : ∀ i < 16 * n, s₁₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₈.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi' => by
      rw [fa.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hi', m₁₀b, m₁₀a, m₉]
  obtain hdata' : DInv s₀.mem s₁₀.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) g E) :=
    fun i hi' => by rw [hmem i hi']; exact hdata i hi'
  obtain mem₉' : s₁₀b.mem = s₈.mem := by rw [m₁₀b, m₁₀a, m₉]
  obtain sc₁₀ : ScrOk s₀ b g E s₁₀.mem := (mem₉' ▸ sc₈).frame hfit' fa dsTab
  obtain g₁₀' : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .eax → s₁₀.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [g₁₀, o₁₀b r h2, o₁₀a r h1, o₉ r h3, g₈ r h4 h5 h3 h6, o₆ r h1 h2 h3,
        cs₅ r (mem_calleeSaved h1 h2 h3 h4 h5 h6), g₄, g₃ r h4 h5 h3 h6, o₁ r h1 h2 h3]
  obtain base₁₀ : s₁₀.gpr .edi = b := by
    rw [g₁₀' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain esp₁₀ : s₁₀.gpr .esp = s₀.gpr .esp := by
    rw [g₁₀' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.esp]
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₁₀b, rd₁₀a, rd₉, rd₈, hi.rd]
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₁₀b', hi.wr]
  obtain fr : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩, below (s₀.gpr .esp) 16] s₀.mem s₁₀.mem := by
    refine fr₄.trans ((f₅.sub fun r hr => ?_).trans
      ((f₈.sub fun r hr => ⟨⟨D.setWidth 64, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (mem₉' ▸ fa.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, sc₁₀, by have := hdata'; rw [hn] at this; exact this, fr, rd₁₀', wr₁₀'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, ?_, ?_, by omega_arith, sc₁₀,
      by rw [show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata', fr, rd₁₀', wr₁₀'⟩
    · rw [dp₁₀, o₁₀b _ (by decide), r₁₀a, o₉ _ (by decide), esi₈]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [np₁₀, r₁₀b, ebp₁₀a, ecx₁₀a, VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

/-- The data loop. -/
theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n R : Nat} {g : Nat} {E : Nat → BitVec 64} {dir : Dir}
    {ws : List (BitVec 64)} (hp : GPre s₀ b D n R) (hg : R / 6 = g) (hE : ∀ i, E i = ws.getD (permOf dir g i) 0)
    {s : State} (hi : GInv s₀ b D n g E 0 s) :
    WP isa (.loop Impl.Camellia.X86.group .ne) s (GDone s₀ b D n g E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n g E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_arith, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hg hE hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

end VG.Proof.Camellia.X86

end

end


/-!
# Camellia ECB on x86 (32-bit): the whole function

As SM4's (`Proof/Sm4/X86/Ecb.lean`) and ARMv7's
(`Proof/Camellia/Arm/Ecb.lean`): `ecb_wp`, with the working space as the
fifth argument and 16 bytes of stack below the return address for the
frames of its calls (`ecbX86`), `ecb dir` saves the callee-saved registers,
builds the table of subkeys for 18 or 24 rounds in the order `dir` uses
them (`table_wp`), keeps the data pointer and the count in their slots,
transforms the blocks a group at a time (`dataGroups_wp`, `dataLoop_wp`) and
restores the registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_)
open VG.Proof.Camellia (DInv outF blocksAt_of_dinv ecb_eq outF_spec schedWords_getD dirPerm dirPerm_lt)

/-- ECB on x86 with its working space as the fifth argument, and 16 bytes of
stack below the return address. -/
def ecbX86 (dir : Dir) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ 16 ≤ (s.gpr .esp).toNat
  post s s' :=
    Spec.Camellia.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (specDir dir)
        (Spec.Camellia.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4)
    (hk : KeyPre s₀ b sched) (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4)
    (hr : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) :
    WP isa (keys dir g) s₀ (KeysPost s₀ b sched g (permOf dir g)) := by
  cases dir
  · exact encKeys_wp hg hk harg hr
  · exact decKeys_wp hg hk harg hr

/-! ## The arguments -/

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat} (hi : i < 5) :
    (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_arith),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_arith)]
  exact VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- … and within it. -/
theorem arg_sub (s : State) (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat} (hi : i < 5) :
    Region.Sub ⟨argAddr s i, 4⟩ ⟨argAddr s 0, 20⟩ := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_arith),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_arith)]
  exact VG.Offset.sub _ (by omega_arith) (by omega_arith)

/-- The 16 bytes below the stack pointer, as the contract writes them. -/
theorem below_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    below (s.gpr .esp) 16 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ := by
  show (⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth h]

/-- … apart from the return address. -/
theorem below_ret {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (below (s.gpr .esp) 16) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  rw [below_eq h]; exact (VG.Offset.base_disjoint_below _ (by decide)).symm

/-- `mov eax, [esp + 4 + 4 i]; mov [edi + 4 k], eax`. -/
theorem argSlot_ok (s : State) {b : BitVec 32} {i k : Nat} (hb : s.gpr .edi = b) (hk : k < slots)
    (hw : ScrIn s.wr b) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] s = some s' ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp i)) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (s.ea (argOp i)) 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (k := k) (by rw [o₁ _ (by decide), hb]) hk
    (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, by rw [g₂, v₁], fun r hr => by rw [g₂, o₁ r hr], by rw [m₂, v₁, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], by rw [← m₁]; exact f₂⟩
  rw [show ([.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.store (slotAt .edi k) .eax] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- `mov eax, [esp + 8]; cmp eax, 18`. -/
theorem cmpRounds_ok (s : State) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)] s = some s' ∧
      s'.zf = some (s.mem.readW (s.ea (argOp 1)) 32 - 18 == 0) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 1 ha
  let a := s₁.gpr .eax
  refine ⟨arithFlags s₁ (a - 18) (a.toNat < (18 : BitVec 32).toNat) (subOverflow a 18 (a - 18)), ?_,
    by rw [RegUpd.zf_arithFlags, show a = _ from v₁], fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr],
    by rw [RegUpd.mem_arithFlags, m₁], by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  rw [show ([.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)] : List Instr) =
    [.mov .eax (.mem (argOp 1))] ++ [.alu .cmp .eax (.imm 18)] from rfl, runBlock_app, e₁, Option.bind_some]
  rfl

/-! ## The table and the groups -/

/-- What the body needs: the prologue's work. -/
structure BodyPre (s₀ : State) (b sched D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem table_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) {g : Nat} (hg : g = 3 ∨ g = 4) {s₁ : State}
    (h₁ : BodyPre s₀ (arg s₀ 4) (arg s₀ 0) (arg s₀ 2) (arg s₀ 3).toNat s₁) :
    WP isa (keys dir g) s₁ (KeysPost s₁ (arg s₀ 4) (arg s₀ 0) g (permOf dir g)) := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE, hR, -, -, -, -⟩ := hp
  obtain hwS : ScrIn s₀.wr (arg s₀ 4) := .exact (by rw [hwr]; simp) fitB
  obtain hrK : (⟨(arg s₀ 0).setWidth 64, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  obtain hrA : (⟨argAddr s₀ 0, 20⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  exact keys_wp dir hg ⟨h₁.base, by rw [h₁.wr]; exact hwS, List.mem_append_left _ (by rw [h₁.rd]; exact hrK), fitK, dKS⟩
    (by rw [h₁.rd, h₁.wr, ea_arg h₁.esp]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE (i := 0) (by decide)⟩)
    (by rw [ea_arg h₁.esp]; exact h₁.frame.readW (arg_contains s₀ fitE (i := 0) (by decide)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide))

theorem dataGroups_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) {g : Nat} (hg : g = 3 ∨ g = 4)
    (hgR : (arg s₀ 1).toNat / 6 = g) {s₁ s₂ : State}
    (h₁ : BodyPre s₀ (arg s₀ 4) (arg s₀ 0) (arg s₀ 2) (arg s₀ 3).toNat s₁)
    (k₂ : KeysPost s₁ (arg s₀ 4) (arg s₀ 0) g (permOf dir g) s₂) :
    WP isa Impl.Camellia.X86.groups s₂ (GDone s₀ (arg s₀ 4) (arg s₀ 2) (arg s₀ 3).toNat g
      fun i => (schedWords s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat).getD (permOf dir g i) 0) := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE, hR, sD, sS, sA, s16⟩ := hp
  let sched := arg s₀ 0
  let R := (arg s₀ 1).toNat
  let D := arg s₀ 2
  let n := (arg s₀ 3).toNat
  let b := arg s₀ 4
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (sched.setWidth 64) R).getD (permOf dir g i) 0
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  obtain hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨sched.setWidth 64, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain hrA : (⟨argAddr s₀ 0, 20⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 5,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 5,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  obtain subS : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    fun k hk => slot_sub hfit' hk
  obtain hk₁ : KeyPre s₁ b sched :=
    ⟨h₁.base, by rw [h₁.wr]; exact hwS, List.mem_append_left _ (by rw [h₁.rd]; exact hrK), fitK, dKS⟩
  unfold Impl.Camellia.X86.groups
  obtain f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₂.mem :=
    h₁.frame.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [k₂.regs _ (by decide) (by decide), h₁.esp]
  obtain hE : ∀ i < 8 * g + 2,
      Spec.Camellia.wordAt s₁.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * permOf dir g i)) = E i :=
    fun i hi => by
      obtain hp : permOf dir g i < 8 * g + 2 := dirPerm_lt (specDir dir) hi
      rw [show E i = _ from schedWords_getD s₀.mem (sched.setWidth 64) (R := R)
        (by simp only [Spec.Camellia.scheduleLength]; omega_arith)]
      exact hk₁.wordAt_eq h₁.frame (by omega_arith)
  obtain sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨hg, fun i hi => hE i hi ▸ by rw [← base₂]; exact base₂ ▸ k₂.ent i hi, fun i hi => ?_⟩
    rw [← h₁.saved i hi]
    exact slot_keep hfit' (lo := savedSlot) (hi := slots) (Nat.le_refl _) k₂.frame
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by rw [savedSlot_eq, slots_eq] at *; omega_arith))
      (by omega_arith) (by rw [savedSlot_eq, slots_eq]; omega_arith)
  obtain rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, h₁.rd]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, h₁.wr]
  -- The data pointer and the count to their slots.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a, f₃a⟩ := argSlot_ok s₂ (i := 2) (k := dSlot) base₂ (by decide)
    (by rw [wr₂]; exact hwS) (argIn rd₂ wr₂ esp₂ 2 (by decide))
  obtain f₀₃a : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃a.mem :=
    f₀₂.trans (f₃a.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact subS _ (by decide)⟩)
  obtain esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b, f₃b⟩ := argSlot_ok s₃a (i := 3) (k := nSlot)
    ((o₃a _ (by decide)).trans base₂) (by decide) (by rw [wr₃a, wr₂]; exact hwS)
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 3 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .eax &&& s₃b.gpr .eax) false false
  obtain e₃ : runBlock isa [.mov .eax (.mem (argOp 2)), st dSlot .eax, .mov .eax (.mem (argOp 3)), st nSlot .eax,
      .alu .test .eax (.reg .eax)] s₂ = some s₃ := by
    rw [show ([.mov .eax (.mem (argOp 2)), st dSlot .eax, .mov .eax (.mem (argOp 3)), st nSlot .eax,
        .alu .test .eax (.reg .eax)] : List Instr) =
      [.mov .eax (.mem (argOp 2)), .store (slotAt .edi dSlot) .eax] ++
        ([.mov .eax (.mem (argOp 3)), .store (slotAt .edi nSlot) .eax] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_app, e₃a, Option.bind_some, runBlock_app, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain eax₃ : s₃b.gpr .eax = arg s₀ 3 := by
    rw [a₃b, ea_arg esp₃a]; exact argR f₀₃a 3 (by decide)
  obtain dp₃ : s₃.mem.readW (wordAddr b dSlot) 32 = D := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := dSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_right (by decide),
      m₃a, readW_slot_write hfit' (j := dSlot) (k := dSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ea_arg esp₂]
    exact argR f₀₂ 2 (by decide)
  obtain np₃ : s₃.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 n := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := nSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ← a₃b, eax₃]
    simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain f₃ : Frame [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩] s₂.mem s₃.mem :=
    (f₃a.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (f₃b.sub fun r hr => ⟨r, by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  obtain sc₃ : ScrOk s₀ b g E s₃.mem := sc₂.frame hfit' f₃ (dn_disj hfit')
  obtain f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₀₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, dn_sub hfit' r hr⟩)
  obtain data₃ : ∀ i < 16 * n, s₃.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₀₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega_arith) hi
  obtain fr₃ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩, below (s₀.gpr .esp) 16] s₀.mem s₃.mem :=
    f₀₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain g₃ : ∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r := fun r hr => by
    show s₃b.gpr r = _; rw [o₃b r hr, o₃a r hr]
  obtain base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide)]; exact base₂
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), esp₂]
  obtain rd₃ : s₃.rd = s₀.rd := by show s₃b.rd = _; rw [rd₃b, rd₃a, rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by show s₃b.wr = _; rw [wr₃b, wr₃a, wr₂]
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [RegUpd.zf_arithFlags, eax₃, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  -- The groups.
  refine WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, sc₃, fun i hi => by omega_arith, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    obtain hstk := below_eq (s := s₀) s16
    refine dataLoop_wp (dir := dir) (ws := schedWords s₀.mem (sched.setWidth 64) R)
      ⟨hwS, hwD, dDS, fitD, hR, ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE (i := 1) (by decide)⟩,
        by show arg s₀ 1 = _; simp, dAS.sub_left (arg_sub s₀ fitE (by decide)),
        dAD.sub_left (arg_sub s₀ fitE (by decide)), by rw [hstk]; exact sS, by rw [hstk]; exact sD,
        by rw [hstk]; exact sA.sub_right (arg_sub s₀ fitE (by decide)), s16⟩ hgR (fun _ => rfl)
      ⟨base₃, esp₃, by rw [dp₃]; simp,
      by rw [np₃, Nat.mul_zero, Nat.sub_zero], by omega_arith, sc₃, fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega_arith)]

/-! ## The function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' := by
  have hp' := hp
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE, hR, sD, sS, sA, s16⟩ := hp
  let sched := arg s₀ 0
  let R := (arg s₀ 1).toNat
  let D := arg s₀ 2
  let n := (arg s₀ 3).toNat
  let b := arg s₀ 4
  obtain hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  obtain hrA : (⟨argAddr s₀ 0, 20⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 5,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 5,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 4) hwS (argIn rfl rfl rfl 4 (by decide))
    (by rw [ea_arg rfl]; rfl)
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain ⟨s₂, e₂, z₂, o₂, m₂, rd₂, wr₂⟩ := cmpRounds_ok s₁ (argIn rd₁ wr₁ esp₁ 1 (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  obtain hz₂ : s₂.zf = some (decide (R = 18)) := by
    rw [z₂, ea_arg esp₁, argR f₁ 1 (by decide), show arg s₀ 1 = BitVec.ofNat 32 R by simp [R],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega_arith) (by decide)]
  obtain hb₂ : BodyPre s₀ b sched D n s₂ :=
    ⟨by rw [o₂ _ (by decide), b₁], by rw [o₂ _ (by decide), esp₁], by rw [m₂]; exact sv₁, by rw [m₂]; exact f₁,
      by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  obtain hg : g = 3 ∨ g = 4 := by omega_arith
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (sched.setWidth 64) R).getD (permOf dir g i) 0
  refine WP.seq (WP.mono (M := isa) (Q := KeysPost s₂ b sched g (permOf dir g))
    (WP.ite (decide (R = 18)) ((eval_e s₂).trans hz₂) (fun h => ?_) (fun h => ?_)) fun s₃ k₃ => ?_)
  · obtain rfl : g = 3 := by simp at h; omega_arith
    exact table_wp dir hp' (.inl rfl) hb₂
  · obtain rfl : g = 4 := by simp at h; omega_arith
    exact table_wp dir hp' (.inr rfl) hb₂
  refine WP.seq (WP.mono (dataGroups_wp dir hp' hg hgR hb₂ k₃) fun s₅ (d₅ : GDone s₀ b D n g E s₅) => ?_)
  -- The epilogue.
  obtain ⟨s₆, e₆, rg₆, o₆, m₆, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [d₅.wr]; exact hwS) d₅.base
    d₅.scr.saved
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), d₅.esp]
  · rw [m₆]
    exact d₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dRS
      · exact dRD
      · exact (below_ret s16).symm) (by decide)
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) g E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Camellia.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Camellia.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    subst hgR
    exact outF_spec (specDir dir) s₀.mem (sched.setWidth 64) (D.setWidth 64) hR j

end VG.Proof.Camellia.X86
