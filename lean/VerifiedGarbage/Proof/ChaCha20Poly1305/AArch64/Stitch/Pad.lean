module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Body
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20 and Poly1305 together (AArch64): the keystream while absorbing other data

`Stitch.bulkPad`: `Mixed8.enter`, one chunk of the kernel whose phases absorb
the 448 bytes from `x2` (`Stitch.chunkPad`, by `chunkWith_ok`: the chunk keeps
`x2` in `x19`, from which the phases point `x20` at the bytes), and
`Mixed8.leave`. The registers `enter` saves are restored, the chunk's data
(`x1`, 512 bytes) is XORed with the keystream of eight blocks from the
state's counter, and the accumulator has absorbed the 448 bytes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Chunked source sr br dr scalarBuf)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

/-- What `bulkPad` needs: the kernel's regions (`CP` but for `x20`, which
`enter` sets), the working space 64 bytes after the state, and the 448 bytes
from `x2` readable and apart from the state and the working space. -/
structure PadPre (s : State) : Prop where
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  vectorRead : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
    (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 512 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (sr s).Disjoint (br s)
  st_d : (sr s).Disjoint (dr s)
  d_b : (dr s).Disjoint (br s)
  x3 : s.gpr .x3 = s.gpr .x0 + 64#64
  blk : ∀ d, d + 8 ≤ 448 → InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 d) 8
  win : ∀ r ∈ [sr s, br s], (⟨s.gpr .x2, 448⟩ : Region).Disjoint r

/-- The registers `Mixed8.enter` saves, and where in the working space. -/
abbrev gpSlots : List (Reg × Nat) := [(.x20, 256), (.x19, 264), (.x26, 272)]

theorem enter_eq : VG.Impl.ChaCha20.AArch64.Mixed8.enter =
    Spill.saveCode .x3 gpSlots ++ (([.addImm .x .x20 .x3 0] : List Instr) ++
      VG.Proof.ChaCha20.AArch64.Mixed8.saveV) := rfl

theorem leave_eq : VG.Impl.ChaCha20.AArch64.Mixed8.leave =
    VG.Proof.ChaCha20.AArch64.Mixed8.restoreV ++ Spill.restoreCode .x3 gpSlots := rfl

/-- After `enter`. -/
structure Entered (s e : State) : Prop where
  x20 : e.gpr .x20 = s.gpr .x3
  gpr : ∀ r, r ≠ .x20 → e.gpr r = s.gpr r
  v : e.v = s.v
  rd : e.rd = s.rd
  wr : e.wr = s.wr
  sp : e.sp = s.sp
  frame : Frame (enterR s) s.mem e.mem
  saved : Spill.Saved (s.gpr .x3) s.gpr gpSlots e.mem
  v8 : e.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s.v .v8
  v9 : e.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s.v .v9

theorem enter_ok (s : State)
    (hb : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.enter) s (Entered s) := by
  rw [enter_eq]
  refine Spill.save_ok (by decide) (fun p hp => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact hb _ 8 (by decide)
  let s₁ : State := { s with mem := Spill.saveMem s.mem (s.gpr .x3) s.gpr gpSlots }
  let a : State := s₁.write .x .x20 (s₁.gpr .x3 + BitVec.ofNat 64 0)
  apply WP.block_cons_iff.mpr
  refine ⟨a, by simpa only [State.read, BitVec.setWidth_eq] using
    exec_addImm_x (s := s₁) (d := .x20) (n := .x3) (imm := 0) (by decide), ?_⟩
  have ha3 : a.gpr .x3 = s.gpr .x3 := RegUpd.gpr_write_of_ne _ .x _ (by decide)
  have haw : a.wr = s.wr := rfl
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok a (by rw [haw, ha3]; exact hb 128 16 (by decide))
    (by rw [haw, ha3]; exact hb 144 16 (by decide))).mono
    fun u ⟨hg, hv, hr, hw, hsp, hf, h8, h9⟩ => ?_
  simp only [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR, ha3] at hf h8 h9
  have f₁ : Frame [⟨s.gpr .x3 + BitVec.ofNat 64 256, 24⟩] s.mem a.mem :=
    Spill.saveMem_frame (lo := 256) (n := 24) (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide) (by decide) _ _ _
  have hsv : Spill.Saved (s.gpr .x3) s.gpr gpSlots u.mem :=
    (Spill.saveMem_saved (by decide) s.mem (s.gpr .x3) s.gpr).frame hf (fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by decide) (by decide) (by decide))
  refine ⟨?_, fun r hr => ?_, by rw [hv]; rfl, by rw [hr]; rfl, by rw [hw]; rfl, by rw [hsp]; rfl,
    ?_, hsv, h8, h9⟩
  · rw [hg, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · rw [hg, RegUpd.gpr_write_of_ne _ .x _ hr]
  · exact (f₁.mono (by simp [enterR])).trans (hf.mono (by simp [enterR]))

/-- What `bulkPad` leaves: the registers it saves restored, the chunk's data
XORed with the keystream, and the 448 bytes from `x2` absorbed. -/
structure Padded (R a : Nat) (s u : State) : Prop where
  x0 : u.gpr .x0 = s.gpr .x0
  x1 : u.gpr .x1 = s.gpr .x1
  x2 : u.gpr .x2 = s.gpr .x2
  x3 : u.gpr .x3 = s.gpr .x3
  cs : ∀ r ∈ preserved, r ∉ accRegs → u.gpr r = s.gpr r
  v8 : u.v .v8 = s.v .v8
  v9 : u.v .v9 = s.v .v9
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  cnt : source u = source s
  data : ∀ k < 512, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
    s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (VG.Spec.ChaCha20.serialize (VG.Spec.ChaCha20.block (ctr (source s) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s, br s, dr s] s.mem u.mem
  acc : Acc R (absorbAll R a (bytesAt s.mem (s.gpr .x2) 448)) u

/-- An offset of the working space, as an offset of the state. -/
theorem x3_off {s : State} (h : s.gpr .x3 = s.gpr .x0 + 64#64) (d : Nat) :
    s.gpr .x3 + BitVec.ofNat 64 d = s.gpr .x0 + BitVec.ofNat 64 (64 + d) := by
  rw [h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bulkPad_ok {R a : Nat} (s : State) (hp : PadPre s) (ha : Acc R a s) :
    WP isa (bulkPad sve) s (Padded R a s) := by
  have hx3 := x3_off hp.x3
  -- Regions, as offsets of the state.
  have hbr : br s = ⟨s.gpr .x0 + BitVec.ofNat 64 64, 320⟩ := by
    simp only [br]; rw [← hx3 0, BitVec.add_zero]
  have hsb : (scalarBuf s).Sub (br s) := Region.sub_prefix (by decide)
  have hkb : (keyR s).Sub (br s) := by
    rw [hbr]; exact Offset.sub _ (by decide) (by decide)
  have henter : ∀ r ∈ enterR s, r.Sub (br s) := by
    intro r hr; simp only [enterR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)
  have hkey_st : (keyR s).Disjoint (sr s) := by
    simp only [keyR, sr]
    rw [show s.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  unfold bulkPad
  apply WP.seq
  refine (enter_ok s hp.buffer).mono fun e he => ?_
  have e0 : e.gpr .x0 = s.gpr .x0 := he.gpr _ (by decide)
  have e1 : e.gpr .x1 = s.gpr .x1 := he.gpr _ (by decide)
  have e2 : e.gpr .x2 = s.gpr .x2 := he.gpr _ (by decide)
  have e3 : e.gpr .x3 = s.gpr .x3 := he.gpr _ (by decide)
  have esr : sr e = sr s := by simp only [sr, e0]
  have ebr : br e = br s := by simp only [br, e3]
  have edr : dr e = dr s := by simp only [dr, e1]
  have esb : scalarBuf e = scalarBuf s := by simp only [scalarBuf, e3]
  have ekey : keyR e = keyR s := by simp only [keyR, e0]
  have erw : e.rd ++ e.wr = s.rd ++ s.wr := by rw [he.rd, he.wr]
  -- The chunk's precondition.
  have hcp : CP e := by
    refine ⟨by rw [he.x20, e3], fun k => ?_, fun k => ?_, ?_, fun d n h => ?_, fun d n h => ?_,
      by rw [esr, ebr]; exact hp.st_b, by rw [esr, edr]; exact hp.st_d,
      by rw [edr, ebr]; exact hp.d_b⟩
    · rw [erw, e0]; exact hp.read k
    · rw [erw, e0]; exact hp.vectorRead k
    · rw [he.wr, e0]; exact hp.counter
    · rw [he.wr, e3]; exact hp.buffer d n h
    · rw [he.wr, e1]; exact hp.data d n h
  have hblk (d : Nat) (h : d + 8 ≤ 448) : InRegions (e.rd ++ e.wr) (s.gpr .x2 + BitVec.ofNat 64 d) 8 := by
    rw [erw]; exact hp.blk d h
  have hk (d : Nat) (hd : d = Poly.r0Off ∨ d = Poly.r1Off) :
      InRegions (e.rd ++ e.wr) (e.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := hp.buffer (160 + (d - 224)) 8 (by rcases hd with rfl | rfl <;> decide)
    refine ⟨r, by rw [erw]; exact List.mem_append_right _ hr, ?_⟩
    rw [e0, show s.gpr .x0 + BitVec.ofNat 64 d = s.gpr .x3 + BitVec.ofNat 64 (160 + (d - 224)) by
      rw [hx3]; rcases hd with rfl | rfl <;> rfl]
    exact hc
  have hwin (d n : Nat) (h : d + n ≤ 448) :
      ∀ r ∈ [sr e, scalarBuf e], (⟨s.gpr .x2 + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hs : (⟨s.gpr .x2 + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨s.gpr .x2, 448⟩ := Offset.sub_base _ h
    rcases hr with rfl | rfl
    · rw [esr]; exact (hp.win _ (by simp)).sub_left hs
    · rw [esb]; exact ((hp.win _ (by simp)).sub_left hs).sub_right hsb
  have pre : ChunkPreW (.addImm .x .x20 .x19 0) (.addImm .x .x20 .x19 256) (s.gpr .x2)
      (s.gpr .x2 + BitVec.ofNat 64 256) (16 * (1 + 5 * 3)) (16 * (2 + 5 * 2)) e := by
    refine ⟨hcp, by rw [he.x20, e0, hp.x3], fun u h19 _ => ?_, fun u h19 _ => ?_,
      fun d h => hblk d (by omega), fun d h => ?_, hk _ (.inl rfl), hk _ (.inr rfl), ?_, ?_,
      by decide, by decide, ?_⟩
    · rw [exec_addImm_x (by decide)]
      simp only [State.read, BitVec.setWidth_eq, h19, e2, BitVec.add_zero]
    · rw [exec_addImm_x (by decide)]
      simp only [State.read, BitVec.setWidth_eq, h19, e2]
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hblk _ (by omega)
    · simpa only [BitVec.add_zero] using hwin 0 256 (by decide)
    · exact hwin 256 192 (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [ekey]
      rcases hr with rfl | rfl | rfl
      · rw [esr]; exact hkey_st
      · rw [esb]
        simp only [keyR, scalarBuf]
        rw [hp.x3]
        exact Offset.disjoint _ (by decide) (by decide) (by decide)
      · rw [edr]; exact (hp.d_b.sub_right hkb).symm
  -- The accumulator, through `enter`.
  have hkey_enter : ∀ r ∈ enterR s, (keyR s).Disjoint r := by
    intro r hr
    simp only [enterR, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [keyR]
    rcases hr with rfl | rfl <;> rw [hx3] <;>
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have hea : Acc R a e :=
    ha.frame (fun r hr => he.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide))
      (fun d hd => rword_frame he.frame e0 hkey_enter d hd)
  -- The chunk.
  apply WP.seq
  refine (chunkWith_ok (sve := sve) e pre hea).mono fun g ⟨hg, hga⟩ => ?_
  have g0 : g.gpr .x0 = s.gpr .x0 := hg.x0.trans ((rebase_of (by decide)).trans e0)
  have g1 : g.gpr .x1 = s.gpr .x1 := hg.x1.trans ((rebase_of (by decide)).trans e1)
  have g2 : g.gpr .x2 = s.gpr .x2 := hg.x2.trans ((rebase_of (by decide)).trans e2)
  have g3 : g.gpr .x3 = s.gpr .x3 := hg.x3.trans ((rebase_of (by decide)).trans e3)
  have gfr : Frame [sr s, scalarBuf s, dr s] e.mem g.mem := by
    have f := hg.frame
    simp only [sr, scalarBuf, dr, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide),
      rebase_of (show Reg.x1 ∉ accRegs by decide), rebase_of (show Reg.x3 ∉ accRegs by decide),
      e0, e1, e3] at f
    exact f
  have grd : g.rd = s.rd := by rw [hg.rd, rebase_rd, he.rd]
  have gwr : g.wr = s.wr := by rw [hg.wr, rebase_wr, he.wr]
  -- What `enter` saved, kept by the chunk.
  have hsv : Spill.Saved (s.gpr .x3) s.gpr gpSlots g.mem :=
    he.saved.frame gfr fun p hp' r hr => by
      have hs : (⟨s.gpr .x3 + BitVec.ofNat 64 p.2, 8⟩ : Region).Sub (br s) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> exact Offset.sub_base _ (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_b.symm.sub_left hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.d_b.symm.sub_left hs
  have hvr (d : Nat) (hd : d = 128 ∨ d = 144) :
      g.mem.read (s.gpr .x3 + BitVec.ofNat 64 d) 16 = e.mem.read (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    have hs : (⟨s.gpr .x3 + BitVec.ofNat 64 d, 16⟩ : Region).Sub (br s) := by
      rcases hd with rfl | rfl <;> exact Offset.sub_base _ (by decide)
    refine gfr.read (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_b.symm.sub_left hs
    · rcases hd with rfl | rfl <;> exact Offset.disjoint_base _ (by decide) (by decide)
    · exact hp.d_b.symm.sub_left hs
  -- `leave`.
  rw [leave_eq]
  have hin (d n : Nat) (h : d + n ≤ 320) :
      InRegions (g.rd ++ g.wr) (g.gpr .x3 + BitVec.ofNat 64 d) n := by
    obtain ⟨r, hr, hc⟩ := hp.buffer d n h
    exact ⟨r, by rw [gwr]; exact List.mem_append_right _ hr, by rw [g3]; exact hc⟩
  refine WP.block_append_iff.mpr ((VG.Proof.ChaCha20.AArch64.Mixed8.restoreV_ok (s.v .v8) (s.v .v9)
    (hin 128 16 (by decide)) (hin 144 16 (by decide))
    (by rw [g3, hvr 128 (.inl rfl), he.v8]) (by rw [g3, hvr 144 (.inr rfl), he.v9])).mono
    fun w ⟨w8, w9, wg, wm, wrd, wwr, wsp⟩ => ?_)
  refine (Spill.restore_wp (b := .x3) (B := s.gpr .x3) (by rw [wg, g3]) (by decide) (by decide)
    (fun p hp' => ?_) (by rw [wm]; exact hsv)).mono fun u hu => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    have := hin
    rw [g3, ← wrd, ← wwr] at this
    rcases hp' with rfl | rfl | rfl <;> exact this _ 8 (by decide)
  have u_of (r : Reg) (h20 : r ≠ .x20) (h19 : r ≠ .x19) (h26 : r ≠ .x26) : u.gpr r = g.gpr r := by
    rw [hu.other r (by simp [h20, h19, h26]), wg]
  have um : u.mem = g.mem := by rw [hu.mem, wm]
  have hdis_enter : ∀ (R : Region), R.Disjoint (br s) → ∀ r ∈ enterR s, R.Disjoint r :=
    fun R hR r hr => hR.sub_right (henter r hr)
  have hsrc : source e = source s := by
    simp only [source, e0]
    exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame he.frame (hdis_enter _ hp.st_b)
  have hsrcg : source (rebase e g) = source s := by
    simp only [source, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide)]
    exact hsrc
  refine ⟨by rw [u_of _ (by decide) (by decide) (by decide), g0],
    by rw [u_of _ (by decide) (by decide) (by decide), g1],
    by rw [u_of _ (by decide) (by decide) (by decide), g2],
    by rw [u_of _ (by decide) (by decide) (by decide), g3], fun r hr hna => ?_,
    by rw [hu.v, w8], by rw [hu.v, w9], by rw [hu.rd, wrd, grd], by rw [hu.wr, wwr, gwr],
    by rw [hu.sp, wsp, hg.sp, rebase_sp, he.sp], ?_, fun k hk => ?_, ?_, ?_⟩
  · by_cases h20 : r = .x20
    · subst h20; exact hu.gpr (.x20, 256) (by simp)
    by_cases h19 : r = .x19
    · subst h19; exact hu.gpr (.x19, 264) (by simp)
    by_cases h26 : r = .x26
    · subst h26; exact hu.gpr (.x26, 272) (by simp)
    rw [u_of r h20 h19 h26, hg.cs r hr h19 h26, rebase_of hna, he.gpr r h20]
  · simp only [source, um, u_of _ (show Reg.x0 ≠ .x20 by decide) (by decide) (by decide), g0]
    have hcn := hg.cnt
    simp only [source, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide), g0, e0] at hcn
    rw [hcn]
    simpa only [source, e0] using hsrc
  · have d := hg.data k hk
    simp only [rebase_mem, rebase_of (show Reg.x1 ∉ accRegs by decide), e1] at d
    rw [um, d, hsrcg, he.frame.bytes (R := dr s) (hdis_enter _ hp.d_b) (by show 512 ≤ 2 ^ 64; decide) hk]
  · rw [um]
    refine (he.frame.sub fun r hr => ⟨br s, by simp, henter r hr⟩).trans (gfr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sr s, by simp, fun _ h => h⟩
    · exact ⟨br s, by simp, hsb⟩
    · exact ⟨dr s, by simp, fun _ h => h⟩
  · have hwe (d n : Nat) (h : d + n ≤ 448) :
        bytesAt e.mem (s.gpr .x2 + BitVec.ofNat 64 d) n = bytesAt s.mem (s.gpr .x2 + BitVec.ofNat 64 d) n :=
      bytesAt_frame he.frame (hdis_enter _ ((hp.win _ (by simp)).sub_left (Offset.sub_base _ h)))
        (by omega)
    have hwe0 := hwe 0 256 (by decide)
    rw [BitVec.add_zero] at hwe0
    rw [show 16 * (1 + 5 * 3) = 256 from rfl, show 16 * (2 + 5 * 2) = 192 from rfl, hwe0,
      hwe 256 192 (by decide), ← Poly1305.bytesAt_add] at hga
    refine hga.frame (fun r hr => ?_) (fun d _ => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact u_of _ (by decide) (by decide) (by decide)
    · simp only [Poly.rword, um, u_of _ (show Reg.x0 ≠ .x20 by decide) (by decide) (by decide)]

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
