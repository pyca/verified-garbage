module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Args
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Rounds
public import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Setup
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Rounds
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Store
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `ChaCha20.AArch64.Mixed8.Chunk`, which this module and modules that import it used -/

section

/-! ### `ChaCha20.AArch64.Rows6.Finish`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Neon4 (output output_word byte_vword)

theorem output_byte (vs : Nat → CState) (k : Nat) :
    (output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 =
      (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [byte_vword _ (by omega_using []),output_word _ _ (by omega_using []),
    VG.Proof.ChaCha20.serialize_getD _ (by omega_using [])]
  simp only [show k / 16 / 4 = k / 64 by omega_using [],
    show 4 * (k / 16 % 4) + k % 16 / 4 = k % 64 / 4 by omega_using [],
    show k % 16 % 4 = k % 64 % 4 by omega_using []]

/-- The six blocks' keystream XORed with the 384 bytes of the source (at `r`)
into the destination (at `x1`), which is the source or apart from it. -/
theorem finishBlocksFrom_ok (r : Reg) {s : State} {blocks : Nat → CState} (h : Holds (pack blocks) s)
    (halias : s.gpr r = s.gpr .x1 ∨ (⟨s.gpr r,384⟩ : Region).Disjoint ⟨s.gpr .x1,384⟩)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block ((List.finRange 24).flatMap (xorRowFrom r))) s fun u =>
      (∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr r + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (blocks (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1,384⟩] s.mem u.mem ∧ StoreSame s u := by
  have hv : ∀ k : Fin 24, s.v (vreg k) = output blocks k.val := by
    intro k
    apply vec_ext
    intro j hj
    rw [h k j hj,pack_get,output_word _ _ hj]
    simp only [Nat.mod_eq_of_lt hj]
  refine (xorListFrom_ok r (List.finRange 24) (List.nodup_finRange 24)
    (VG.Proof.ChaCha20.AArch64.Neon4.DataTo.nil s.mem (s.gpr r) (s.gpr .x1) 384 (output blocks))
    rfl rfl halias hv (fun _ _ => List.not_mem_nil) (fun k _ => hin k) (fun k _ => hout k)).mono
    fun u ⟨hu,hs⟩ => ⟨?_,hu.frame,hs⟩
  intro k hk
  have hm : k / 16 ∈ (List.finRange 24).map Fin.val ++ [] := by
    apply List.mem_append_left
    exact List.mem_map_of_mem (f := Fin.val) (List.mem_finRange (⟨k / 16,by omega_using [hk]⟩ : Fin 24))
  rw [hu _,VG.Offset.add_sub_cancel_left,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hk] : k < 2 ^ 64),
    ite_eq_left ⟨hm,hk⟩,output_byte]

end VG.Proof.ChaCha20.AArch64.Rows6

end

end

/-! ### `ChaCha20.AArch64.Mixed8.Finish`, which only this module used -/

section

/-! ### `ChaCha20.AArch64.Mixed8.Spill2`, which only this module used -/

section

/-! ### `ChaCha20.AArch64.Mixed8.Second`, which only this module used -/

section

/-! ### `ChaCha20.AArch64.Mixed8.Spill`, which only this module used -/

section

/-! ### `ChaCha20.AArch64.Mixed8.Prepare`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs saveArgs_ok counter_ok keeps_vectors scalarLoad_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock)

abbrev source (s : State) : CState := stateAt s.mem (s.gpr .x0)
abbrev sr (s : State) : Region := ⟨s.gpr .x0,64⟩
abbrev br (s : State) : Region := ⟨s.gpr .x3,320⟩
abbrev dr (s : State) : Region := ⟨s.gpr .x1,512⟩

structure CP (s : State) : Prop where
  x20 : s.gpr .x20 = s.gpr .x3
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  vectorRead : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
    (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 512 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (sr s).Disjoint (br s)
  st_d : (sr s).Disjoint (dr s)
  d_b : (dr s).Disjoint (br s)

structure Prepared (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun j => Nat.repeat innerBlock n (ctr (source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock (2 * n) (ctr (source s₀) 6)) s
  cnt : source s = ctr (source s₀) 6
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀] s₀.mem s.mem

 theorem prepare_ok (s : State) (hp : CP s) : WP isa prepare s (Prepared s) := by
  apply WP.seq
  refine (saveArgs_ok s).mono fun a ⟨hsaved,hg,hm₀,hr,hw,hv,hsp⟩ => ?_
  obtain ha : source a = source s := by
    rw [source,hm₀,hg _ (by decide) (by decide)]
  obtain hi : ∀ k : Fin 24, InRegions (a.rd ++ a.wr)
      (a.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [hg _ (by decide) (by decide),hr,hw]; exact hp.vectorRead k
  obtain hca : InRegions (a.rd ++ a.wr) (a.gpr .x0 + 48) 4 := by
    change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4
    rw [hg _ (by decide) (by decide),hr,hw]; exact hp.read 12
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.setup_ok a hi hca).mono fun b ⟨hb,hab,hbt⟩ => ?_
  obtain h0 : b.gpr .x0 = s.gpr .x0 := by rw [hab.gpr _ (by decide),hg _ (by decide) (by decide)]
  obtain hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.rd,hab.wr,h0,hr,hw]; exact hp.read 12
  obtain hco : InRegions b.wr (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.wr,hw,h0]; exact hp.counter
  apply WP.seq
  refine (counter_ok b (n := 6) (by decide) false hc hco).mono fun c
    ⟨hcm,hcg,hcr,hcw,hcv,hcsp⟩ => ?_
  obtain hcnt : source c = ctr (source s) 6 := by
    rw [source,hcg _ (by decide),hcm]
    change stateAt (b.mem.writeW (b.gpr .x0 + BitVec.ofNat 64 48)
      (b.mem.readW (b.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 6)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    change ctr (source b) 6 = _
    rw [source,hab.mem,hab.gpr _ (by decide)]
    exact congrArg (fun v => ctr v 6) ha
  obtain hfc : Frame [sr s] b.mem c.mem := by
    rw [hcm,h0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  obtain hcs : SavedArgs (s.gpr .x2) (s.gpr .x1) c := by
    exact ⟨by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.len,
      by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.data⟩
  obtain hpc : VG.Proof.ChaCha20.AArch64.Pre c := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (c.rd ++ c.wr) (c.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcr,hcw,hab.rd,hab.wr,hr,hw,hcg _ (by decide),h0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcw,hab.wr,hw,hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide)]
      exact hp.data _ _ (by omega_using [hk])
    · change (⟨c.gpr .x1,256⟩ : Region).Disjoint ⟨c.gpr .x0,64⟩
      rw [hcg _ (by decide),hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide),h0]
      exact hp.st_d.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 512))
  obtain hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i
    rfl
  refine (keeps_vectors hload (scalarLoad_ok c hpc)).mono fun d ⟨⟨hd,hm,hdrr,hdwr,hdk⟩,hdv,hdsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,hdrr.trans (hcr.trans (hab.rd.trans hr)),
    hdwr.trans (hcw.trans (hab.wr.trans hw)),hdsp.trans (hcsp.trans (hab.sp.trans hsp)),?_⟩
  · intro k j hj
    rw [hdv,hcv]
    have hbb : VG.Proof.ChaCha20.AArch64.Rows6.Holds
        (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => ctr (source a) j)) b := hb
    rw [ha] at hbb
    exact hbb k j hj
  · rw [hdv,hcv,hbt]
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat] using hd
  · rw [source,hm,hdk _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact hcnt
  · exact ⟨by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.len,
      by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.data⟩
  · intro r hnr h21 h22
    rw [hdk r hnr,hcg r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),
      hab.gpr r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),hg r h21 h22]
  · rw [hm]
    rw [hab.mem,hm₀] at hfc
    exact hfc

end VG.Proof.ChaCha20.AArch64.Mixed8

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs move_ok keeps_vectors scalarFinish_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev lowBuf (s : State) : Region := ⟨s.gpr .x3,64⟩

structure Spilled (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds
    (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 5 (ctr (source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  cnt : source s = ctr (source s₀) 6
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  words : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 6))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,lowBuf s₀] s₀.mem s.mem

theorem spill_ok {s₀ s : State} (hp : CP s₀) (h : Prepared s₀ s 5) :
    WP isa (spill 0) s (Spilled s₀) := by
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide)
  obtain nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  obtain hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (move_ok s .x1 .x20).mono fun a ⟨ha,hav,hasp⟩ => ?_
  obtain hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (source s₀) 6)) a := by
    intro k hk
    rw [ha.other _ (by
      intro he; exact VG.Proof.ChaCha20.AArch64.not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  obtain hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.rd,ha.wr,h.rd,h.wr,ha.other _ (by decide),hx0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.wr,h.wr,ha.gpr,hx20]
      exact hp.buffer _ _ (by omega_using [hk])
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  obtain hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by
    decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  obtain hfb : Frame [lowBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  obtain hcntₐ : source a = ctr (source s₀) 6 := by
    rw [source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  obtain hcntb : source b = ctr (source s₀) 6 := by
    rw [source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))]
    exact hcntₐ
  obtain hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,?_,hcntb,hsavedb,?_,?_,?_,
    hr.trans (ha.rd.trans h.rd),hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  · rw [hbv,hav]; exact h.table
  · intro k hkk
    obtain he := hb k hkk
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr hr1 h21 h22; rw [hk r hnr,ha.other r hr1,h.keep r hnr h21 h22]
  · rw [hk _ VG.Proof.ChaCha20.AArch64.not_words_x1,ha.gpr,hx20]
  · rw [ha.mem] at hfb
    exact (h.frame.mono (by simp)).trans (hfb.mono (by simp))

end VG.Proof.ChaCha20.AArch64.Mixed8

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs counter_ok scalarLoad_ok keeps_vectors)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

variable {sve : Bool}

structure Second (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun j => Nat.repeat innerBlock (5 + n) (ctr (source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock (2 * n) (ctr (source s₀) 7)) s
  cnt : source s = ctr (source s₀) 7
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  first : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 6))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 →
    s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,lowBuf s₀] s₀.mem s.mem

theorem reload_ok {s₀ s : State} (hp : CP s₀) (h : Spilled s₀ s) :
    WP isa (.seq (.block (VG.Impl.ChaCha20.AArch64.Mixed5.counter 1))
      (.block VG.Impl.ChaCha20.AArch64.load)) s (Second s₀) := by
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 :=
    h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  obtain hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.rd,h.wr,hx0]; exact hp.read 12
  obtain ho : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.wr,hx0]; exact hp.counter
  apply WP.seq
  refine (counter_ok s (n := 1) (by decide) false hc ho).mono fun a
    ⟨hm,hg,hr,hw,hv,hsp⟩ => ?_
  obtain hcnt : source a = ctr (source s₀) 7 := by
    rw [source,hg _ (by decide),hm]
    change stateAt (s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 48)
      (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 1)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    change ctr (source s) 1 = _
    rw [h.cnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add]
  obtain hf : Frame [sr s₀] s.mem a.mem := by
    rw [hm,hx0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  obtain hfirst : ∀ k (hk : k < 16),
      a.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
        (block (ctr (source s₀) 6))[k] := by
    intro k hk
    rw [hf.readW (r := lowBuf s₀) (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
      (by intro r hr'; have he := List.mem_singleton.mp hr'; subst r
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide)]
    exact h.words k hk
  obtain hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hr,hw,h.rd,h.wr,hg _ (by decide),hx0]; exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hw,h.wr,hg _ (by decide),h.x1]; exact hp.buffer _ _ (by omega_using [hk])
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [hg _ (by decide),h.x1,hg _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  obtain hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i; rfl
  refine (keeps_vectors hload (scalarLoad_ok a hpₐ)).mono fun b
    ⟨⟨hb,hbm,hbr,hbw,hbk⟩,hbv,hbsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hbr.trans (hr.trans h.rd),
    hbw.trans (hw.trans h.wr),hbsp.trans (hsp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hv,Nat.add_zero] using h.vec
  · rw [hbv,hv]; exact h.table
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat,Nat.mul_zero] using hb
  · rw [source,hbm,hbk _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact hcnt
  · exact ⟨by rw [hbk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),hg _ (by decide)]; exact h.saved.len,
      by rw [hbk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),hg _ (by decide)]; exact h.saved.data⟩
  · rw [hbm]; exact hfirst
  · intro r hnr h1 h19 h26
    rw [hbk r hnr,hg r (by intro he; subst r; exact hnr ⟨2,by decide,rfl⟩)]
    exact h.keep r hnr h1 h19 h26
  · rw [hbk _ VG.Proof.ChaCha20.AArch64.not_words_x1,hg _ (by decide)]; exact h.x1
  · rw [hbm]; exact h.frame.trans (hf.mono (by simp))

theorem second_ok {s₀ s : State} (hp : CP s₀) (h : Prepared s₀ s 5) :
    WP isa second s (Second s₀) := by
  apply WP.seq
  exact (spill_ok hp h).mono fun _ h => reload_ok hp h

theorem compute_second_ok {s₀ s : State} (hp : CP s₀) (h : Second s₀ s) :
    WP isa (phase sve .x20) s fun u => Second s₀ u 5 := by
  refine (counted_phase_ok h.vec h.scalar h.table
    (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)) (by decide)
    (h.x1.trans ((h.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))
      (by decide) (by decide) (by decide)).trans hp.x20).symm)).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  have he (f : CState → CState) (x : CState) : Nat.repeat f 5 (Nat.repeat f 5 x) = Nat.repeat f 10 x := rfl
  obtain hv : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j))) u := by
    obtain he' : (fun j => Nat.repeat innerBlock 5 (Nat.repeat innerBlock 5 (ctr (source s₀) j))) =
        (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) :=
      funext fun j => he innerBlock (ctr (source s₀) j)
    rw [he'] at hu
    exact hu
  refine ⟨hv,hut,hr.holds,?_,?_,?_,?_,?_,hr.rd.trans h.rd,hr.wr.trans h.wr,hsp.trans h.sp,?_⟩
  · rw [source,hr.mem,hr.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact h.cnt
  · exact ⟨by rw [hr.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hr.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩
  · rw [hr.mem]; exact h.first
  · intro r hnr h1 h19 h26; rw [hr.keep r hnr]; exact h.keep r hnr h1 h19 h26
  · rw [hr.keep _ VG.Proof.ChaCha20.AArch64.not_words_x1]; exact h.x1
  · rw [hr.mem]; exact h.frame

end VG.Proof.ChaCha20.AArch64.Mixed8

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs keeps_vectors scalarFinish_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev scalarBuf (s : State) : Region := ⟨s.gpr .x3,128⟩
abbrev highBuf (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 64,64⟩

theorem move_offset_ok (s : State) (d n : Reg) (offset : Nat) (ho : offset < 4096) :
    WP isa (.block [.addImm .x d n offset]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u d (s.gpr n + BitVec.ofNat 64 offset) ∧
      u.v = s.v ∧ u.sp = s.sp := by
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 offset),?_,
    WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
  simpa only [State.read,BitVec.setWidth_eq] using
    exec_addImm_x (s := s) (d := d) (n := n) (imm := offset) ho

structure Spilled2 (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds
    (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j))) s
  cnt : source s = ctr (source s₀) 7
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  first : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 6))[k]
  last : ∀ k (hk : k < 16), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 7))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 →
    s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,scalarBuf s₀] s₀.mem s.mem

theorem spill2_ok {s₀ s : State} (hp : CP s₀) (h : Second s₀ s 5) :
    WP isa (spill 64) s (Spilled2 s₀) := by
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 :=
    h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  obtain nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  obtain hx20 : s.gpr .x20 = s₀.gpr .x3 :=
    (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (move_offset_ok s .x1 .x20 64 (by decide)).mono fun a ⟨ha,hav,hasp⟩ => ?_
  obtain hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (source s₀) 7)) a := by
    intro k hk
    rw [ha.other _ (by
      intro he; exact VG.Proof.ChaCha20.AArch64.not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  obtain hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.rd,ha.wr,h.rd,h.wr,ha.other _ (by decide),hx0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.wr,h.wr,ha.gpr,hx20,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hp.buffer _ _ (by omega_using [hk])
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Offset.sub_base _ (by decide : 64 + 256 ≤ 320))
  obtain hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  obtain hfb : Frame [highBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  obtain hcntₐ : source a = ctr (source s₀) 7 := by
    rw [source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  obtain hcntb : source b = ctr (source s₀) 7 := by
    rw [source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Offset.sub_base _ (by decide : 64 + 64 ≤ 320)))]
    exact hcntₐ
  obtain hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,hcntb,hsavedb,?_,?_,?_,hr.trans (ha.rd.trans h.rd),
    hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  · intro k hk'
    rw [hfb.readW (r := lowBuf s₀) (Offset.contains_base _ (by omega_using [hk']) (by omega_using [hk']))
      (by intro r hr'; have he := List.mem_singleton.mp hr'; subst r
          exact Offset.base_disjoint _ (by decide : 64 ≤ 64) (by decide : 64 + 64 ≤ 2 ^ 64)) (by decide),ha.mem]
    exact h.first k hk'
  · intro k hk'
    obtain he := hb k hk'
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr h1 h19 h26; rw [hk r hnr,ha.other r h1]; exact h.keep r hnr h1 h19 h26
  · rw [ha.mem] at hfb
    obtain hf₀ : Frame [sr s₀,scalarBuf s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr'; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨sr s₀,by simp,fun _ h => h⟩
      · exact ⟨scalarBuf s₀,by simp,Region.sub_prefix (by decide : 64 ≤ 128)⟩)
    exact hf₀.trans (hfb.sub (by
      intro r hr'; have he := List.mem_singleton.mp hr'; subst r
      exact ⟨scalarBuf s₀,by simp,Offset.sub_base _ (by decide : 64 + 64 ≤ 128)⟩))

theorem Spilled2.words {s₀ s : State} (h : Spilled2 s₀ s) (k : Nat) (hk : k < 32) :
    s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
      (block (ctr (source s₀) (6 + k / 16)))[k % 16]'(by omega_using []) := by
  by_cases hk' : k < 16
  · simpa only [Nat.div_eq_of_lt hk',Nat.mod_eq_of_lt hk',Nat.add_zero] using h.first k hk'
  · have he := h.last (k - 16) (by omega_using [hk])
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 64 + 4 * (k - 16) = 4 * k by omega_using [hk']] at he
    simpa only [show k / 16 = 1 by omega_using [hk, hk'],show k % 16 = k - 16 by omega_using [hk, hk']] using he

theorem Spilled2.read16 {s₀ s : State} (h : Spilled2 s₀ s) (r : Fin 8) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun j => block (ctr (source s₀) (6 + j))) r := by
  rw [VG.AArch64.read16]
  obtain hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (block (ctr (source s₀) (6 + r.val / 4)))[4 * (r.val % 4) + e]'(by omega_using [he]) := by
    intro e he
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega_using [],
      h.words _ (by omega_using [he])]
    simp only [show (4 * r.val + e) / 16 = r.val / 4 by omega_using [he],
      show (4 * r.val + e) % 16 = 4 * (r.val % 4) + e by omega_using [he]]
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed8

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (restoreArgs_ok counter_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev firstR (s : State) : Region := ⟨s.gpr .x1,384⟩

/-- The source of a chunk, at `r`: `x1` itself (in place, the destination),
or `x27` (`vg_chacha20_xor`'s chunks, whose `x1` is the destination): readable,
apart from the state and the working space, and the destination or apart from
it. -/
structure SrcOK (r : Reg) (s : State) : Prop where
  reg : r = .x1 ∨ r = .x27
  src : ∀ d n, d + n ≤ 512 → InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 d) n
  st_s : (sr s).Disjoint ⟨s.gpr r,512⟩
  s_b : (⟨s.gpr r,512⟩ : Region).Disjoint (br s)
  alias : s.gpr r = s.gpr .x1 ∨ (⟨s.gpr r,512⟩ : Region).Disjoint (dr s)

/-- In place. -/
theorem CP.src {s : State} (hp : CP s) : SrcOK .x1 s :=
  ⟨.inl rfl, fun d n h => by obtain ⟨q,hq,hc⟩ := hp.data d n h; exact ⟨q,List.mem_append_right _ hq,hc⟩,
    hp.st_d, hp.d_b, .inl rfl⟩

/-- After the vector blocks' keystream is XORed with the source (at `r`)
into the destination (at `x1`). -/
structure FinishedFrom (r : Reg) (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  buf : ∀ r : Fin 8, s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
    VG.Proof.ChaCha20.AArch64.Neon4.output (fun j => block (ctr (source s₀) (6 + j))) r
  data : ∀ k < 384, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr r + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,scalarBuf s₀,firstR s₀] s₀.mem s.mem

theorem finishFrom_ok (r : Reg) {s₀ s : State} (hp : CP s₀) (hs : SrcOK r s₀) (h : Spilled2 s₀ s) :
    WP isa (vectorFinishFrom r) s (FinishedFrom r s₀) := by
  obtain nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  obtain hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  apply WP.seq
  refine (restoreArgs_ok s h.saved).mono fun a
    ⟨ha1,ha2,ha3,hag,ham,har,haw,hav,hasp⟩ => ?_
  obtain ha0 : a.gpr .x0 = s₀.gpr .x0 := (hag _ (by decide) (by decide) (by decide)).trans hx0
  obtain ha₃ : a.gpr .x3 = s₀.gpr .x3 := ha3.trans hx20
  obtain har' : a.rd = s₀.rd := har.trans h.rd
  obtain haw' : a.wr = s₀.wr := haw.trans h.wr
  obtain hcnta : source a = ctr (source s₀) 7 := by
    rw [source,ham,hag _ (by decide) (by decide) (by decide)]; exact h.cnt
  obtain hc : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [har',haw',ha0]; exact hp.read 12
  obtain hco : InRegions a.wr (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [haw',ha0]; exact hp.counter
  apply WP.seq
  refine (counter_ok a (n := 7) (by decide) true hc hco).mono fun b
    ⟨hbm,hbg,hbr,hbw,hbv,hbsp⟩ => ?_
  obtain hb0 : b.gpr .x0 = s₀.gpr .x0 := (hbg _ (by decide)).trans ha0
  obtain hcntb : source b = source s₀ := by
    rw [source,hbg _ (by decide),hbm]
    change stateAt (a.mem.writeW (a.gpr .x0 + BitVec.ofNat 64 48)
      (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 48) 32 - BitVec.ofNat 32 7)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      ← VG.Proof.ChaCha20.AArch64.Xor.stateAt_getElem_counter]
    change (source a).set 12 ((source a)[12] - BitVec.ofNat 32 7) = _
    rw [hcnta,ctr,Vector.getElem_set_self,BitVec.add_sub_cancel,Vector.set_set,
      Vector.set_getElem_self]
  obtain hfb : Frame [sr s₀] a.mem b.mem := by
    rw [hbm,ha0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  obtain hv : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j))) b := by
    simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  obtain hin : ∀ k : Fin 24, InRegions (b.rd ++ b.wr)
      (b.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [hbr,hbw,har',haw',hb0]; exact hp.vectorRead k
  obtain hctr : InRegions (b.rd ++ b.wr) (b.gpr .x0 + 48) 4 := by
    change InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4
    rw [hbr,hbw,har',haw',hb0]; exact hp.read 12
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.feedForward_ok b hin hctr).mono fun c ⟨hvc,hbc⟩ => ?_
  obtain hcb0 : c.gpr .x0 = s₀.gpr .x0 := (hbc.gpr _ (by decide)).trans hb0
  obtain hcb1 : c.gpr .x1 = s₀.gpr .x1 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha1)
  obtain hcb3 : c.gpr .x3 = s₀.gpr .x3 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha₃)
  obtain hrc : c.rd = s₀.rd := hbc.rd.trans (hbr.trans har')
  obtain hwc : c.wr = s₀.wr := hbc.wr.trans (hbw.trans haw')
  obtain hvc' : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => block (ctr (source s₀) j))) c := by
    intro k j hj
    rw [hvc k j hj,hv k j hj,VG.Proof.ChaCha20.AArch64.Rows6.input_ctr b k j hj]
    change _ + (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun q => ctr (source b) q) j)[k] = _
    rw [hcntb]
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.pack_get,block,Vector.getElem_zipWith]
  obtain hout : ∀ k : Fin 24, InRegions c.wr
      (c.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [hwc,hcb1]; exact hp.data _ _ (by omega_using [])
  obtain hcbr : c.gpr r = s₀.gpr r := by
    rcases hs.reg with rfl | rfl
    · exact hcb1
    · rw [hbc.gpr _ (by decide),hbg _ (by decide),hag _ (by decide) (by decide) (by decide)]
      exact h.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by simp [preserved]))
        (by decide) (by decide) (by decide)
  obtain hin : ∀ k : Fin 24, InRegions (c.rd ++ c.wr)
      (c.gpr r + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [hrc,hwc,hcbr]; exact hs.src _ _ (by omega_using [])
  obtain halias : c.gpr r = c.gpr .x1 ∨ (⟨c.gpr r,384⟩ : Region).Disjoint ⟨c.gpr .x1,384⟩ := by
    rw [hcbr,hcb1]
    rcases hs.alias with he | hd
    · exact .inl he
    · exact .inr ((hd.sub_left (Region.sub_prefix (by decide : 384 ≤ 512))).sub_right
        (Region.sub_prefix (by decide : 384 ≤ 512)))
  refine (VG.Proof.ChaCha20.AArch64.Rows6.finishBlocksFrom_ok r hvc' halias hin hout).mono
    fun d ⟨hd,hfd,hcd⟩ => ?_
  obtain hfd' : Frame [firstR s₀] c.mem d.mem := by simpa only [hcb1] using hfd
  obtain hfc : Frame [sr s₀] s.mem c.mem := by rw [hbc.mem,← ham]; exact hfb
  obtain hpre : Frame [sr s₀,scalarBuf s₀] s₀.mem c.mem :=
    h.frame.trans (hfc.mono (by simp))
  refine ⟨(congrFun hcd.gpr _).trans hcb0,(congrFun hcd.gpr _).trans hcb1,?_,
    (congrFun hcd.gpr _).trans hcb3,?_,hcd.rd.trans hrc,hcd.wr.trans hwc,
    hcd.sp.trans (hbc.sp.trans (hbsp.trans (hasp.trans h.sp))),?_,?_,?_,
    (hpre.mono (by simp)).trans (hfd'.mono (by simp))⟩
  · rw [hcd.gpr,hbc.gpr _ (by decide),hbg _ (by decide),ha2]
  · intro r hr h21 h22
    obtain n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    obtain n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    obtain n3 : r ≠ .x3 := by intro he; subst r; simp [preserved] at hr
    obtain n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    rw [hcd.gpr,hbc.gpr r n4,hbg r n4,hag r n1 n2 n3]
    exact h.keep r (VG.Proof.ChaCha20.AArch64.not_words_preserved hr) n1 h21 h22
  · rw [source,hcd.gpr,hcb0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfd' (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right (Region.sub_prefix (by decide : 384 ≤ 512))),hbc.mem]
    rw [← hb0]; exact hcntb
  · intro r
    rw [hfd'.read (r := scalarBuf s₀) (Offset.contains_base _ (by omega_using []) (by omega_using []))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact (hp.d_b.sub_left (Region.sub_prefix (by decide : 384 ≤ 512))).symm.sub_left
            (Region.sub_prefix (by decide : 128 ≤ 320))) (by decide),
      hfc.read (r := scalarBuf s₀) (Offset.contains_base _ (by omega_using []) (by omega_using []))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 128 ≤ 320))) (by decide)]
    exact h.read16 r
  · intro k hk
    rw [hcb1,hcbr] at hd
    rw [hd k hk,hpre.bytes (R := ⟨s₀.gpr r,512⟩) (by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      · exact hs.st_s.symm
      · exact hs.s_b.sub_right (Region.sub_prefix (by decide : 128 ≤ 320)))
      (by change 512 ≤ 2 ^ 64; decide) (by change k < 512; omega_using [hk])]

end VG.Proof.ChaCha20.AArch64.Mixed8

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (serialize block)

variable {sve : Bool}

abbrev lastR (s : State) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 384,128⟩

/-- After a chunk: its 512 bytes of the source (at `r` on entry) XORed with
the keystream of its eight blocks into the destination (at `x1`). -/
structure ChunkedFrom (r : Reg) (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  data : ∀ k < 512, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr r + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,scalarBuf s₀,dr s₀] s₀.mem s.mem

theorem lastFrom_ok (r : Reg) {s₀ s : State} (hp : CP s₀) (hsr : SrcOK r s₀) (h : FinishedFrom r s₀ s) :
    WP isa (.block ((List.finRange 8).flatMap (xorScalarRowFrom r))) s (ChunkedFrom r s₀) := by
  obtain hr : s.gpr r = s₀.gpr r := by
    rcases hsr.reg with rfl | rfl
    · exact h.x1
    · exact h.cs _ (by simp [preserved]) (by decide) (by decide)
  obtain hi : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k
    rw [h.rd,h.wr,h.x3]
    obtain ⟨r,hr,hc⟩ := hp.buffer (16 * k.val) 16 (by omega_using [])
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  obtain hs : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    intro k; rw [h.rd,h.wr,hr]; exact hsr.src _ _ (by omega_using [])
  obtain ho : ∀ k : Fin 8, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    intro k; rw [h.wr,h.x1]; exact hp.data _ _ (by omega_using [])
  obtain hdis : (scalarBuf s₀).Disjoint (lastR s₀) :=
    (hp.d_b.symm.sub_left (Region.sub_prefix (by decide : 128 ≤ 320))).sub_right
      (Offset.sub_base _ (by decide : 384 + 128 ≤ 512))
  obtain hsl : Region.Sub ⟨s₀.gpr r + BitVec.ofNat 64 384,128⟩ ⟨s₀.gpr r,512⟩ :=
    Offset.sub_base _ (by decide : 384 + 128 ≤ 512)
  obtain halias : s₀.gpr r + BitVec.ofNat 64 384 = (lastR s₀).base ∨
      (⟨s₀.gpr r + BitVec.ofNat 64 384,128⟩ : Region).Disjoint ⟨(lastR s₀).base,128⟩ := by
    rcases hsr.alias with he | hd
    · exact .inl (by rw [he])
    · exact .inr ((hd.sub_left hsl).sub_right (Offset.sub_base _ (by decide : 384 + 128 ≤ 512)))
  refine (xorScalarListFrom_ok r (List.finRange 8) (List.nodup_finRange 8)
    (VG.Proof.ChaCha20.AArch64.Neon4.DataTo.nil s.mem (s₀.gpr r + BitVec.ofNat 64 384)
      (lastR s₀).base 128 _)
    (by rw [hr]) (by rw [h.x1]) h.x3 hdis halias
    (fun _ _ => List.not_mem_nil) hi hs ho).mono fun u ⟨hu,hs⟩ => ?_
  obtain hf : Frame [lastR s₀] s.mem u.mem := data_frame128 hu
  obtain hst : (sr s₀).Disjoint (lastR s₀) :=
    hp.st_d.sub_right (Offset.sub_base _ (by decide : 384 + 128 ≤ 512))
  refine ⟨(congrFun hs.gpr _).trans h.x0,(congrFun hs.gpr _).trans h.x1,
    (congrFun hs.gpr _).trans h.x2,(congrFun hs.gpr _).trans h.x3,?_,
    hs.rd.trans h.rd,hs.wr.trans h.wr,hs.sp.trans h.sp,?_,?_,?_⟩
  · intro r hr h19 h26; rw [hs.gpr]; exact h.cs r hr h19 h26
  · rw [source,hs.gpr,h.x0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
      intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hst)]
    rw [← h.x0]; exact h.cnt
  · intro k hk
    by_cases hk' : k < 384
    · rw [hf.bytes (R := firstR s₀) (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r
        exact Offset.base_disjoint _ (by decide : 384 ≤ 384) (by decide : 384 + 128 ≤ 2 ^ 64))
        (by decide : 384 ≤ 2 ^ 64) hk',h.data k hk']
    · have htail : k - 384 < 128 := by omega_using [hk]
      obtain he : (lastR s₀).base + BitVec.ofNat 64 (k - 384) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        dsimp [lastR]; rw [BitVec.add_assoc,← BitVec.ofNat_add,show 384 + (k - 384) = k by omega_using [hk']]
      obtain hes : s₀.gpr r + BitVec.ofNat 64 384 + BitVec.ofNat 64 (k - 384) =
          s₀.gpr r + BitVec.ofNat 64 k := by
        rw [BitVec.add_assoc,← BitVec.ofNat_add,show 384 + (k - 384) = k by omega_using [hk']]
      obtain hm := hu ((lastR s₀).base + BitVec.ofNat 64 (k - 384))
      rw [VG.Offset.add_sub_cancel_left,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hk] : k - 384 < 2 ^ 64)] at hm
      obtain hslot : (k - 384) / 16 ∈ (List.finRange 8).map Fin.val ++ [] := by
        apply List.mem_append_left
        exact List.mem_map_of_mem (f := Fin.val)
          (List.mem_finRange (⟨(k - 384) / 16,by omega_using [hk]⟩ : Fin 8))
      rw [ite_eq_left ⟨hslot,by omega_using [hk]⟩,he,hes] at hm
      dsimp only at hm
      obtain hbuf := h.buf (⟨(k - 384) / 16,by omega_using [hk]⟩ : Fin 8)
      rw [hbuf,
        VG.Proof.ChaCha20.AArch64.Rows6.output_byte] at hm
      obtain hplain : s.mem (s₀.gpr r + BitVec.ofNat 64 k) = s₀.mem (s₀.gpr r + BitVec.ofNat 64 k) := by
        obtain hp' := h.frame.bytes (R := ⟨s₀.gpr r + BitVec.ofNat 64 384,128⟩) (by
          intro q hq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact (hsr.st_s.sub_right hsl).symm
          · exact (hsr.s_b.sub_left hsl).sub_right (Region.sub_prefix (by decide : 128 ≤ 320))
          · rcases hsr.alias with he' | hd
            · rw [he']; exact Offset.disjoint_base _ (by decide : 384 ≤ 384) (by decide : 384 + 128 ≤ 2 ^ 64)
            · exact (hd.sub_left hsl).sub_right (Region.sub_prefix (by decide : 384 ≤ 512)))
          (by decide : 128 ≤ 2 ^ 64) htail
        rwa [hes] at hp'
      rw [hplain,show 6 + (k - 384) / 64 = k / 64 by omega_using [hk'],
        show (k - 384) % 64 = k % 64 by omega_using [hk']] at hm
      exact hm
  · have hpre : Frame [sr s₀,scalarBuf s₀,dr s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sr s₀,by simp,fun _ h => h⟩
      · exact ⟨scalarBuf s₀,by simp,fun _ h => h⟩
      · exact ⟨dr s₀,by simp,Region.sub_prefix (by decide : 384 ≤ 512)⟩)
    exact hpre.trans (hf.sub (by
      intro r hr; have he := List.mem_singleton.mp hr; subst r
      exact ⟨dr s₀,by simp,Offset.sub_base _ (by decide : 384 + 128 ≤ 512)⟩))

theorem chunkFrom_ok (r : Reg) (s : State) (hp : CP s) (hs : SrcOK r s) :
    WP isa (chunkFrom sve r) s (ChunkedFrom r s) := by
  apply WP.seq
  refine (prepare_ok s hp).mono fun a ha => ?_
  apply WP.seq
  obtain first : WP isa (phase sve .x26) a fun b => Prepared s b 5 := by
    refine (counted_phase_ok ha.vec ha.scalar ha.table
      (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)) (by decide)
      ((ha.keep _ VG.Proof.ChaCha20.AArch64.not_words_x1 (by decide) (by decide)).trans ha.saved.data.symm)).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
    refine ⟨hv,ht,hc.holds,?_,?_,?_,hc.rd.trans ha.rd,hc.wr.trans ha.wr,hsp.trans ha.sp,?_⟩
    · rw [source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact ha.cnt
    · exact ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact ha.saved.len,
        by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact ha.saved.data⟩
    · intro r hr h19 h26; rw [hc.keep r hr]; exact ha.keep r hr h19 h26
    · rw [hc.mem]; exact ha.frame
  refine first.mono fun b hb => ?_
  apply WP.seq
  refine (second_ok hp hb).mono fun c hc => ?_
  apply WP.seq
  refine (compute_second_ok hp hc).mono fun d hd => ?_
  apply WP.seq
  refine (spill2_ok hp hd).mono fun e he => ?_
  apply WP.seq
  exact (finishFrom_ok r hp hs he).mono fun f hf => lastFrom_ok r hp hs hf

end VG.Proof.ChaCha20.AArch64.Mixed8

end

end

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (stateAt)

/-- The high bit tests the public number of complete blocks against eight.
Dividing the byte count by 64 first makes the test valid for every u64 length. -/
theorem less8 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n >>> 6) - BitVec.ofNat 64 8) >>> 63 =
      BitVec.ofNat 64 (if n < 512 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  have hd : n / 2 ^ 6 < 2 ^ 58 := by omega_using [hn]
  by_cases h : n < 512
  · rw [ite_eq_left h]
    have hb : n / 2 ^ 6 < 8 := by omega_using [h]
    omega_using [h]
  · rw [ite_eq_right h]
    have hb : 8 ≤ n / 2 ^ 6 := by omega_using [h]
    omega_using [hn, h]

theorem check_ok (s : State) :
    WP isa (.block check) s fun u =>
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x5 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, check, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, isa, runStep_some, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_,fun r hr => by simp only [hr,ite_false],rfl,rfl,rfl,rfl,rfl⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using less8 (s.gpr .x2).toNat (s.gpr .x2).isLt

end VG.Proof.ChaCha20.AArch64.Mixed8
