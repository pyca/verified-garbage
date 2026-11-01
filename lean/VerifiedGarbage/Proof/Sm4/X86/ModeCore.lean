module

public import VerifiedGarbage.Proof.Sm4.X86.PreparedVerified
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Impl.Sm4.X86.Modes
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Sm4.X86.PreparedBody
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's core for the modes on x86 (32-bit)

`dirCoreSpec d`: SM4's core for the direction `d` (`Impl.Sm4.X86.dirCore d`)
meets what the modes need of a core (`Proof.Modes.X86.CoreSpec`), with the
key a schedule, read through the first stack argument, its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption,
and the key ready when the table of round keys in `d`'s order is in the
scratch buffer (`ReadyAt`).

`prepare` and `crypt` call `vg_sm4_prepare_keys` and
`vg_sm4_crypt_prepared` (`callWithGpr`, with their contracts on x86,
`prepX86` and `cryptX86`) on the core's slots, their arguments pushed below
`esp`, which the key's arguments and the core's slots are apart from.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.X86.Wp VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (argOp sb)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout write4_apply)
open VG.Proof.Sm4 (scheduleAt_congr bytesAt_eq_blockAt ofFn_toList crypt_eq specDirX86)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- The schedule, at the address in the first stack argument, outside the
regions `rs`, as is that argument; the stack the core's calls use is apart
from both; and the fifth argument the base of each of `rs` (the core's
slots), outside them and the stack. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.Sm4.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 128 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 128⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧
    (∀ r ∈ (⟨p.setWidth 64, 128⟩ : Region) :: rs, Region.Disjoint (stkRegion (s.gpr .esp) 20) r) ∧
    ∃ q : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 4)) 4 ∧ s.mem.readW (s.ea (argOp 4)) 32 = q ∧
      (∀ r ∈ rs, r.base = q.setWidth 64) ∧ (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 4), 4⟩ r) ∧
      Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨s.ea (argOp 4), 4⟩

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

/-- The cipher of `d` on the 16 bytes at `p`: the 32 rounds with the round
keys in `d`'s order. -/
theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) =
      (outBlock (quads .enc (dirKeys d k) 8 (ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.decryptBlock, crypt_eq]; rfl

theorem dirCore_slots (d : Dir) : (dirCore d).slots = 358 := rfl
theorem dirCore_total (d : Dir) : (dirCore d).total = 368 := rfl
theorem dirCore_stack (d : Dir) : (dirCore d).stack = 20 := rfl

/-- The table, ready, the core's slots not wrapping around, and the stack
the calls use apart from them. -/
def Ready (d : Dir) (s : State) (B : BitVec 32) (k : Spec.Sm4.Schedule) : Prop :=
  ReadyAt d s.mem B k ∧ B.toNat + 4 * 368 ≤ 2 ^ 32 ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨B.setWidth 64, 4 * 368⟩

/-- An entry's word, outside the regions apart from the core or within its
buffer. -/
theorem entry_keep {d : Dir} {B : BitVec 32} (hfit : B.toNat + 4 * (dirCore d).total ≤ 2 ^ 32) {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    {e j : Nat} (he : e < 32) (hj : j < 8) : entryW m' B e j = entryW m B e j := by
  rw [dirCore_total] at hfit
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega_arith)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hd r hr with h | h
  · exact h.symm.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, tableSlot_eq, slots_eq]; omega_arith)) |>.symm
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint _ (.inr (by simp only [dirCore, tailSlot_eq, tableSlot_eq]; omega_arith))
      (by rw [tableSlot_eq]; omega_arith) (by simp only [dirCore, tailSlot_eq]; omega_arith)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis, hsdis, q, qin, hq, qbase, qdis, qstk⟩ := h
  have hea : s'.ea (argOp 0) = s.ea (argOp 0) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  have hea4 : s'.ea (argOp 4) = s.ea (argOp 4) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit, hdis,
    by rw [hea]; exact hadis, by rw [hesp]; exact hsdis, q, by rw [hrd, hwr, hea4]; exact qin, ?_, qbase,
    by rw [hea4]; exact qdis, by rw [hesp, hea4]; exact qstk⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hadis (by decide), hp]
  · exact (scheduleAt_congr fun i hi => hf.bytes (R := ⟨p.setWidth 64, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega_arith) hi).symm
  · rw [hea4, hf.readW (Region.contains_self _ _) qdis (by decide), hq]

/-! ## The calls -/

theorem prepare_nosp : NoSp prepareKeys := by
  apply NoSp.of_all
  change prepareKeys.allInstrs _ = true
  lit_decide

theorem crypt_nosp : NoSp cryptPrepared := by
  apply NoSp.of_all
  change cryptPrepared.allInstrs _ = true
  lit_decide

theorem prepare_stack : stackUse prepareKeys = 0 := by
  simp [prepareKeys, keys, encKeys, decKeys, keyLoop, stackUse]

theorem crypt_stack : stackUse cryptPrepared = 0 := by
  simp [cryptPrepared, crypt8, rounds, stackUse]

theorem toNat_wsWords : (BitVec.ofNat 32 wsWords).toNat = 179 := by decide

theorem dirOf_dirFlagOf (d : Dir) : dirOf (BitVec.ofNat 32 (dirFlagOf d)) = d := by cases d <;> decide

theorem dirFlagOf_le (d : Dir) : (BitVec.ofNat 32 (dirFlagOf d)).toNat ≤ 1 := by cases d <;> decide

/-- Writing back the word read from `a` changes nothing. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  rw [write4_apply]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

/-- The table, through memory that differs only apart from the working space. -/
theorem holds_frame {m m' : Mem} {B : BitVec 32} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    {rs : List Region} (h : Holds layout m (B.setWidth 64) k d) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨B.setWidth 64, 4 * slots⟩ r) : Holds layout m' (B.setWidth 64) k d :=
  fun r hr i hi => by
    have hr' := hr
    rw [layout_table, List.mem_singleton] at hr'
    subst hr'
    dsimp only at hi ⊢
    rw [hf.bytes (R := ⟨B.setWidth 64, 4 * slots⟩) hd (by show 4 * slots ≤ 2 ^ 64; rw [slots_eq]; omega_arith)
      (i := 384 + i) (by show 384 + i < 4 * slots; rw [slots_eq]; omega_arith)]
    exact h _ hr i hi

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : Holds layout m B k d) (hk : Proof.Sm4.Prepared.Keeps B 179 layout.cryptScratch m m') :
    Holds layout m' B k d := fun r hr i hi => by
  have hr' := hr
  rw [layout_table, List.mem_singleton] at hr'
  subst hr'
  dsimp only at hi ⊢
  rw [hk (384 + i) (by omega_arith) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [tableSlot_eq, savedSlot_eq, slots_eq]
    omega_arith)]
  exact h _ hr i hi

/-- A block, through memory that differs only apart from it. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : Spec.Sm4.blockAt m' p = Spec.Sm4.blockAt m p := by
  simp only [Spec.Sm4.blockAt]
  congr 1
  funext j
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; omega_arith) j.isLt

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Sm4.blockFn K d (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Sm4.ecb_eq] at this
  simpa [Spec.Sm4.blocksAt, hj] using this

theorem modeDSlot_eq : modeDSlot = 362 := rfl
theorem modeNSlot_eq : modeNSlot = 363 := rfl

theorem below_eq (E : BitVec 32) (n : Nat) : below E n = stkRegion E n := rfl

theorem prepare_wp (d : Dir) {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr VG.Impl.Modes.X86.sb = B) (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hst : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr VG.Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -, hstk, q, qin, hq, qbase, qdis, qstk⟩ := hk
  have hfB := hs.fit
  have hw := hs.wr
  rw [dirCore_total] at hfB hw hR
  have hst' : 20 ≤ (s.gpr .esp).toNat := hst
  have hB' : s.gpr .edi = B := hB
  have hE := (s.gpr .esp).isLt
  have sK : Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨p.setWidth 64, 128⟩ := hstk _ List.mem_cons_self
  have sW : Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨B.setWidth 64, 4 * 368⟩ :=
    hstk _ (List.mem_cons_of_mem _ hR)
  show WP isa (prepareCall d) s _
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_ldm (B := s.gpr .esp)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin)
    fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have edi₃ : s₃.gpr .edi = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  have eax₃ : s₃.gpr .eax = BitVec.ofNat 32 wsWords := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine WP.seq ?_
  have edx₃ : s₃.gpr .edx = BitVec.ofNat 32 (dirFlagOf d) := by rw [u₃.other _ (by decide), u₂.gpr]
  have ecx₃ : s₃.gpr .ecx = p := by rw [u₃.gpr, u₂.mem, u₁.mem]; exact hp
  let rs' : List Reg := [.eax, .edi, .edx, .ecx]
  have hrs : Reg.esp ∉ rs' := by decide
  have fit : 4 * rs'.length + 4 ≤ (s₃.gpr .esp).toNat := by rw [esp₃]; exact hst'
  let sE := (pushed rs' s₃).callEntry
  have a0 : arg sE 0 = p := by rw [callEntry_arg fit hrs (by decide)]; exact ecx₃
  have a1 : arg sE 1 = BitVec.ofNat 32 (dirFlagOf d) := by rw [callEntry_arg fit hrs (by decide)]; exact edx₃
  have a2 : arg sE 2 = B := by rw [callEntry_arg fit hrs (by decide)]; exact edi₃
  have a3 : arg sE 3 = BitVec.ofNat 32 wsWords := by rw [callEntry_arg fit hrs (by decide)]; exact eax₃
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0, esp₃]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by rw [callEntry_esp', esp₃]; rfl
  have b16 : Region.Sub (below (s.gpr .esp) 16) (stkRegion (s.gpr .esp) 20) := below_sub (by decide) hst'
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 20).setWidth 64, 4⟩ (stkRegion (s.gpr .esp) 20) :=
    Region.sub_prefix (by decide)
  have wsSub : Region.Sub ⟨B.setWidth 64, 179 * 8⟩ ⟨B.setWidth 64, 4 * 368⟩ := Region.sub_prefix (by decide)
  refine VG.Proof.Rc2.X86.Cbc.callWithGpr (c := prepareKeys) (k := prepX86) prep_correct prepare_nosp
    (by decide) hrs (by rw [prepare_stack, esp₃]; exact hst')
    (rd := [⟨p.setWidth 64, 128⟩, ⟨argAddr sE 0, 16⟩]) (wr := [⟨B.setWidth 64, 179 * 8⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change prepX86.pre (sE.withRegions _ _)
    simp only [prepX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_wsWords]
    refine ⟨trivial, trivial, (hdis _ hR).sub_right wsSub, (sW.sub_left b16).sub_right wsSub,
      (sW.sub_left r4).sub_right wsSub, hfit, by omega_arith, ?_, dirFlagOf_le d, by rw [size_eq, slots_eq]⟩
    rw [sub_toNat hst']
    omega_arith
  · refine Covers.cons (Covers.of_mem fun r hr => ?_) (Covers.cons (Covers.of_mem fun r hr => ?_)
      (Covers.cons (Covers.of_forall fun r hr => ?_) Covers.nil))
    · rw [List.mem_singleton] at hr; subst hr
      rw [rd₃, wr₃]
      rcases List.mem_append.mp hsch with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · rw [List.mem_singleton] at hr; subst hr
      refine List.mem_append_right _ ?_
      rw [eA, esp₃]
      exact List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact Covers.right (Covers.of_sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (by rw [wr₃]; exact hw), 0, by simp, by show 0 + 179 * 8 ≤ 4 * 368; omega_arith⟩)
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (by rw [wr₃]; exact hw), 0, by simp, by show 0 + 179 * 8 ≤ 4 * 368; omega_arith⟩
  · intro s' rd' wr' cs frame ⟨s₂', mem₂, _, post⟩
    change prepX86.post (sE.withRegions _ _) s₂' at post
    simp only [prepX86, State.withRegions_mem, arg_withRegions, a0, a1, a2, a3, mem₂, toNat_wsWords] at post
    have stackFrame := callEntry_frame fit hrs
    rw [esp₃, m₃] at stackFrame
    change Frame [stkRegion (s.gpr .esp) 20] s.mem sE.mem at stackFrame
    have hsch' : Spec.Sm4.scheduleAt sE.mem (p.setWidth 64) = Spec.Sm4.scheduleAt s.mem (p.setWidth 64) :=
      scheduleAt_congr fun i hi => stackFrame.bytes (R := ⟨p.setWidth 64, 128⟩)
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact sK.symm) (by show 128 ≤ 2 ^ 64; omega_arith) hi
    rw [hsch'] at post
    have esp' : s'.gpr .esp = s.gpr .esp := (cs .esp (by decide)).trans esp₃
    rw [esp₃, m₃, prepare_stack] at frame
    have frame' : Frame [⟨B.setWidth 64, 179 * 8⟩, stkRegion (s.gpr .esp) 20] s.mem s'.mem := frame
    have hqB : q = B := by
      have h1 : B.setWidth 64 = q.setWidth 64 := qbase _ hR
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h1
      simp only [BitVec.toNat_setWidth] at this
      have := B.isLt
      have := q.isLt
      omega_arith
    have hea4 : s'.ea (argOp 4) = s.ea (argOp 4) := by
      show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [esp']
    have hq' : s'.mem.readW (s.ea (argOp 4)) 32 = B := by
      rw [frame'.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (qdis _ hR).sub_right wsSub
        · exact qstk.symm) (by decide), hq, hqB]
    refine wp_ldm (B := s'.gpr .esp) rfl (by show InRegions (s'.rd ++ s'.wr) (s'.ea (argOp 4)) 4; rw [rd', wr', rd₃, wr₃, hea4]; exact qin) fun s₄ u₄ => WP.block_nil ?_
    have g₄ : ∀ r, r ≠ .edi → s₄.gpr r = s'.gpr r := fun r h => u₄.other r h
    have edi₄ : s₄.gpr .edi = B := by rw [u₄.gpr]; exact (congrArg (s'.mem.readW · 32) hea4).trans hq'
    refine ⟨⟨?_, hfB, by rw [g₄ _ (by decide), esp']; exact sW⟩, edi₄, by rw [g₄ _ (by decide), esp'],
      ?_, by rw [u₄.rd, rd', rd₃], by rw [u₄.wr, wr', wr₃]⟩
    · have := readyAt_of_words (words_of_holds (by rw [slots_eq]; omega_arith) post.1)
      rw [ofSpecDir_dirOf, dirOf_dirFlagOf] at this
      rw [u₄.mem]; exact this
    · rw [u₄.mem]
      refine frame.sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, slots_eq]; omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

theorem crypt_wp (d : Dir) {s : State} {B : BitVec 32} {k : Spec.Sm4.Schedule} (hB : s.gpr VG.Impl.Modes.X86.sb = B)
    (hs : VG.Proof.Modes.X86.ScrIn s B (dirCore d).total) (hr : Ready d s B k) (hst : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr VG.Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Ready d s' B k ∧ Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hready, hfB, sW⟩ := hr
  have hw := hs.wr
  rw [dirCore_total] at hw
  have hst' : 20 ≤ (s.gpr .esp).toNat := hst
  have hB' : s.gpr .edi = B := hB
  have hE := (s.gpr .esp).isLt
  have slotIn : ∀ o, o + 4 ≤ 4 * 368 → (⟨B.setWidth 64, 4 * 368⟩ : Region).Contains (addr B o) 4 := fun o h => by
    rw [addr_eq (by omega_arith)]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hH : Holds layout s.mem (B.setWidth 64) k (specDirX86 d) := by
    refine holds_of_words (by rw [slots_eq]; omega_arith) ?_
    rw [ofSpecDir_specDirX86]
    exact words_of_readyAt hready
  show WP isa cryptCall s _
  refine WP.seq ?_
  refine wp_ldm (b := .edi) (o := 4 * modeDSlot) hB'
    ⟨_, List.mem_append_right _ hw, slotIn _ (by rw [modeDSlot_eq]; omega_arith)⟩
    fun s₁ u₁ => wp_ldm (b := .edi) (o := 4 * modeNSlot) ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr]; exact ⟨_, List.mem_append_right _ hw, slotIn _ (by rw [modeNSlot_eq]; omega_arith)⟩)
    fun s₂ u₂ => wp_movi fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have edi₃ : s₃.gpr .edi = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  have eax₃ : s₃.gpr .eax = BitVec.ofNat 32 wsWords := u₃.gpr
  have esi₃ : s₃.gpr .esi = s.mem.readW (addr B (4 * modeDSlot)) 32 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ebp₃ : s₃.gpr .ebp = s.mem.readW (addr B (4 * modeNSlot)) 32 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
  let rs' : List Reg := [.eax, .edi]
  have hrs : Reg.esp ∉ rs' := by decide
  have fit : 4 * rs'.length + 4 ≤ (s₃.gpr .esp).toNat := by rw [esp₃]; show 12 ≤ _; omega_arith
  let sE := (pushed rs' s₃).callEntry
  have a0 : arg sE 0 = B := by rw [callEntry_arg fit hrs (by decide)]; exact edi₃
  have a1 : arg sE 1 = BitVec.ofNat 32 wsWords := by rw [callEntry_arg fit hrs (by decide)]; exact eax₃
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 8).setWidth 64 := by
    rw [callEntry_argAddr0, esp₃]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 12 := by rw [callEntry_esp', esp₃]; rfl
  have b8 : Region.Sub (below (s.gpr .esp) 8) (stkRegion (s.gpr .esp) 20) := below_sub (by decide) hst'
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64, 4⟩ (stkRegion (s.gpr .esp) 20) :=
    fun x hx => below_sub (sp := s.gpr .esp) (a := 12) (b := 20) (by decide) hst' x
      (Region.sub_prefix (len' := 12) (by decide) x hx)
  have wsSub : Region.Sub ⟨B.setWidth 64, 179 * 8⟩ ⟨B.setWidth 64, 4 * 368⟩ := Region.sub_prefix (by decide)
  have stackFrame := callEntry_frame fit hrs
  rw [esp₃, m₃] at stackFrame
  change Frame [stkRegion (s.gpr .esp) 12] s.mem sE.mem at stackFrame
  have s12 : Region.Disjoint (stkRegion (s.gpr .esp) 12) ⟨B.setWidth 64, 4 * 368⟩ :=
    sW.sub_left (below_sub (by decide) hst')
  have hHE : Holds layout sE.mem (B.setWidth 64) k (specDirX86 d) :=
    holds_frame hH stackFrame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (s12.sub_right (Region.sub_prefix (by rw [slots_eq]; decide))).symm
  refine WP.seq ?_
  refine VG.Proof.Rc2.X86.Cbc.callWithGpr (c := cryptPrepared) (k := cryptX86) crypt_correct crypt_nosp
    (by decide) hrs (by rw [crypt_stack, esp₃]; show 12 ≤ _; omega_arith)
    (rd := [⟨argAddr sE 0, 8⟩]) (wr := [⟨B.setWidth 64, 179 * 8⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change cryptX86.pre (sE.withRegions _ _)
    simp only [cryptX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp, toNat_wsWords]
    refine ⟨trivial, trivial, (sW.sub_left b8).sub_right wsSub, (sW.sub_left r4).sub_right wsSub, by omega_arith, ?_,
      by rw [size_eq, slots_eq], k, specDirX86 d, hHE⟩
    rw [sub_toNat (by omega_arith)]
    omega_arith
  · refine Covers.cons (Covers.of_mem fun r hr => ?_) (Covers.cons (Covers.of_forall fun r hr => ?_) Covers.nil)
    · rw [List.mem_singleton] at hr; subst hr
      refine List.mem_append_right _ ?_
      rw [eA, esp₃]
      exact List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact Covers.right (Covers.of_sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (by rw [wr₃]; exact hw), 0, by simp, by show 0 + 179 * 8 ≤ 4 * 368; omega_arith⟩)
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (by rw [wr₃]; exact hw), 0, by simp, by show 0 + 179 * 8 ≤ 4 * 368; omega_arith⟩
  · intro s' rd' wr' cs frame ⟨s₂', mem₂, _, post⟩
    change cryptX86.post (sE.withRegions _ _) s₂' at post
    simp only [cryptX86, State.withRegions_mem, arg_withRegions, a0, a1, mem₂, toNat_wsWords] at post
    obtain ⟨hE', hK⟩ := post
    have hE := hE' k (specDirX86 d) hHE
    rw [esp₃, m₃, crypt_stack] at frame
    have frame' : Frame [⟨B.setWidth 64, 179 * 8⟩, stkRegion (s.gpr .esp) 12] s.mem s'.mem := frame
    have edi' : s'.gpr .edi = B := (cs .edi (by decide)).trans edi₃
    have esp' : s'.gpr .esp = s.gpr .esp := (cs .esp (by decide)).trans esp₃
    have outSlot : ∀ o, 179 * 8 ≤ o → o + 4 ≤ 4 * 368 →
        ∀ r ∈ [(⟨B.setWidth 64, 179 * 8⟩ : Region), stkRegion (s.gpr .esp) 12],
          Region.Disjoint ⟨addr B o, 4⟩ r := fun o h₁ h₂ r hr => by
      rw [addr_eq (by omega_arith)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)
      · exact (s12.sub_right (VG.Offset.sub_base _ (by omega_arith))).symm
    have keepD : s'.mem.readW (addr B (4 * modeDSlot)) 32 = s.mem.readW (addr B (4 * modeDSlot)) 32 :=
      frame'.readW (Region.contains_self _ _) (outSlot _ (by rw [modeDSlot_eq]; omega_arith)
        (by rw [modeDSlot_eq]; omega_arith)) (by decide)
    have keepN : s'.mem.readW (addr B (4 * modeNSlot)) 32 = s.mem.readW (addr B (4 * modeNSlot)) 32 :=
      frame'.readW (Region.contains_self _ _) (outSlot _ (by rw [modeNSlot_eq]; omega_arith)
        (by rw [modeNSlot_eq]; omega_arith)) (by decide)
    have wr'' : s'.wr = s.wr := wr'.trans wr₃
    have inD : InRegions s.wr (addr B (4 * modeDSlot)) 4 := ⟨_, hw, slotIn _ (by rw [modeDSlot_eq]; omega_arith)⟩
    have inN : InRegions s.wr (addr B (4 * modeNSlot)) 4 := ⟨_, hw, slotIn _ (by rw [modeNSlot_eq]; omega_arith)⟩
    refine wp_stm (b := .edi) (B := B) (o := 4 * modeDSlot) edi' (wr'' ▸ inD) fun s₈ u₈ => ?_
    refine wp_stm (b := .edi) (B := B) (o := 4 * modeNSlot) ((congrFun u₈.gpr _).trans edi')
      ((u₈.wr.trans wr'') ▸ inN) fun s₉ u₉ => WP.block_nil ?_
    have m₉ : s₉.mem = s'.mem := by
      rw [u₉.mem, u₈.gpr, u₈.mem, cs .esi (by decide), cs .ebp (by decide), esi₃, ebp₃, ← keepD,
        writeW_readW, ← keepN, writeW_readW]
    have g₉ : ∀ r, s₉.gpr r = s'.gpr r := fun r => by rw [u₉.gpr, u₈.gpr]
    refine ⟨by rw [g₉]; exact edi', by rw [g₉]; exact esp', ⟨?_, hfB, by rw [g₉, esp']; exact sW⟩, ?_,
      fun j hj => ?_, by rw [u₉.rd, u₈.rd, rd', rd₃], by rw [u₉.wr, u₈.wr, wr'']⟩
    · rw [m₉]
      have := readyAt_of_words (words_of_holds (by rw [slots_eq]; omega_arith) (holds_of_keeps hHE hK))
      rw [ofSpecDir_specDirX86] at this
      exact this
    · rw [m₉]
      refine frame'.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, slots_eq]; omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by show 12 ≤ 20; decide) hst'⟩
    · have hj' : j < 8 := hj
      have ha : blkAddr (dirCore d) B j = B.setWidth 64 + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
        simp only [blkAddr, slotA, dirCore, layout, VG.Offset.add_add]
      have hblk : Spec.Sm4.blockAt sE.mem (B.setWidth 64 + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) =
          Spec.Sm4.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) :=
        blockAt_frame stackFrame fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          rw [VG.Offset.add_add]
          exact (s12.sub_right (VG.Offset.sub_base _ (by simp only [layout, tailSlot_eq]; omega_arith))).symm
      rw [show 4 * (dirCore d).bw = 16 from rfl, ha, dirCipher_bytes, bytesAt_eq_blockAt, m₉,
        blockAt_of_ecb hE hj', hblk, quads_spec]

/-- The core's blocks are four words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 4 := rfl

/-- SM4's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := ⟨by simp only [dirCore]; decide, .inr rfl, by simp only [dirCore, slots_eq, tailSlot_eq]; omega_arith,
    by simp only [dirCore]; omega_arith⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h hesp _ _ _ hf _ hd := ⟨fun e he => (h.1 e he).congr fun _ hj => entry_keep h.2.1 hf hd he hj,
    h.2.1, by rw [hesp]; exact h.2.2⟩
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- The core's cipher, without unfolding SM4's: elaborating
`(dirCoreSpec .encrypt).cipher k = Spec.Sm4.cipher k` by unification unfolds
`Spec.Sm4.cipher` first, and evaluates the cipher (seconds; minutes in the
kernel). -/
theorem dirCoreSpec_cipher (d : Dir) : (dirCoreSpec d).cipher = dirCipher d := rfl

end VG.Proof.Sm4.X86
