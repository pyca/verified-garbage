module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.CtPad
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: hashing a message of secret length

`ctHash_vp`: from a state whose `Y` holds the message `msg σ` followed by
zeros up to `nbm` blocks, with its length and `nbm` in their slots, `ctHash`
leaves the digest of the message at `oDig`, keeping any fact about memory
that its writes (`ctW`) do not reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- What `ctHash` writes. -/
abbrev ctW (L : Lay) (scr : BitVec 32) (T : Nat) : List Region :=
  [sR scr oSt (h.N + h.B), L.LOW, sR scr oLen h.B, slotR L sLb, sR scr oY T, sR scr oCW h.H.so,
    sR scr oSel h.N, slotR L sBi, sR scr oDig h.N]

/-- The digest of the hash value at `oSel`, to `oDig`. -/
theorem out_vp (hg : Geo L scr) {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem) (outPart h.H)
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oDig h.N] m₀ s.mem ∧
        s.mem = VG.WriteBytes.writeBytes m₀ (sa scr oDig) (h.md.digest (h.md.stateAt m₀ (sa scr oSel)))) := by
  have hN := h.N_le
  have hN' : h.H.N ≤ 64 := hN
  have fit := hg.fit
  unfold oRsa at fit
  refine VP.taint [.esp, .ebp] h.certs.outPart (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx⟩ => ?_
  simp only [outPart, outSet, atS, addi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
  have c4 : Ctx L scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3
    (by decide) (by decide)).upd u4 (by decide) (by decide)
  have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have bx : t4.gpr .ebx = scr + BitVec.ofNat 32 oSel := by
    simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  have ax : t4.gpr .eax = scr + BitVec.ofNat 32 oDig := by
    simp (disch := decide) only [u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
  have aB : (t4.gpr .ebx).setWidth 64 = sa scr oSel := by rw [bx]; exact hg.scrA (by decide)
  have aA : (t4.gpr .eax).setWidth 64 = sa scr oDig := by rw [ax]; exact hg.scrA (by decide)
  refine WP.mono (h.ok.out t4 (by rw [bx, hg.scr_lt (by decide)]; pomega) (by rw [ax, hg.scr_lt (by decide)]; pomega)
    (by rw [aB]; exact hg.rd c4.st (by pomega)) (by rw [aA]; exact hg.wr c4.st (by pomega))
    (by rw [aB, aA]; exact Geo.sep (by pomega) (by pomega) (by pomega))) fun t ⟨regs, rd, wr, m⟩ => ?_
  rw [aA, aB, m4] at m
  have hl := h.md.digest_length (h.md.stateAt s.mem (sa scr oSel))
  have fr : Frame [sR scr oDig h.N] s.mem t.mem := by
    rw [m]
    intro a ha
    simp only [List.mem_singleton, forall_eq, Region.Contains, VG.WriteBytes.writeBytes, hl] at ha ⊢
    rw [ite_eq_right (by omega)]
  refine ⟨c4.write (by rw [m4]; exact fr) (fun r hr => ?_) rd wr (regs _ (by decide) (by decide))
    (regs _ (by decide) (by decide)), s.mem, hx, fr, m⟩
  simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega)

/-- A byte of our part of `scratch` after bytes are written there. -/
theorem sa_writeBytes (scr : BitVec 32) (m : Mem) {o i : Nat} {xs : List Byte} (hi : i < xs.length)
    (ho : o + i < 2 ^ 64) : VG.WriteBytes.writeBytes m (sa scr o) xs (sa scr (o + i)) = xs.getD i 0 := by
  simp only [VG.WriteBytes.writeBytes, sa, Offset.sub_toNat _ (Nat.le_add_right o i) ho, Nat.add_sub_cancel_left,
    hi, ↓reduceIte]

/-- `ctHash`: the digest of the message in `Y`, of a length in its slot,
padded in `nbm` blocks. -/
theorem ctHash_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame (ctW h L scr (nbm * h.B)) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0)
      (ctHash h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.D, s.mem (sa scr (oDig + i)) = (h.ok.hH.SH.H.hash (msg σ)).getD i 0) := by
  have hN := h.N_le
  have hB := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hNL := h.NL
  have hDN := h.D_le
  have hso := h.so_le
  have fit := hg.fit
  unfold oRsa at fit
  have hB0 : 0 < h.B := by omega
  have hLB : h.L < h.B := by have := h.D_pos; omega
  obtain ⟨σ', ok⟩ := hg.ok
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega
  have hIs : ∀ rs : List Region, (∀ r ∈ rs, r ∈ ctW h L scr (nbm * h.B)) →
      ∀ σ m m', Inv σ m → Frame rs m m' → Inv σ m' :=
    fun rs hs σ m m' hi hf => hI σ m m' hi (hf.mono hs)
  have hq : ∀ σ, ((msg σ).length + h.L) / h.B < nbm := fun σ =>
    (Nat.div_lt_iff_lt_mul hB0).2 (by have := hfit σ; omega)
  have hℓ : ∀ σ, (msg σ).length < 2048 := fun σ => by have := hfit σ; omega
  have sl : ∀ d, d + 4 ≤ frameBytes → ∀ {o n : Nat}, o + n ≤ oRsa → (slotR L d).Disjoint (sR scr o n) :=
    fun d hd o n h => hg.slot ok h (by rw [hg.F]; omega)
  show VP _ (.seq (initPart h.H) (.seq (lenPart h.H) (.seq (padPart h.H) (.seq (compLoop h.H) (outPart h.H))))) _
  -- The hash value initialized.
  refine VP.seq (init_vp h hg (Inv := fun σ m => Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0)
    fun σ m m' ⟨hi, hy⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact hg.low ok (by pomega)) (by pomega) hy⟩) ?_
  -- The length field.
  refine VP.seq (((lenBlk_vp h hg (ℓ := fun σ => (msg σ).length) (Inv := fun σ m =>
      (Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0) ∧
        h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨⟨hi, hy⟩, he⟩ hf => ⟨⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact (sl sLb (by decide) (by pomega)).symm) (by pomega) hy⟩,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact (sl sLb (by decide) (by pomega)).symm).trans he⟩)
    fun σ => by have := hℓ σ; omega)).mono
      (fun σ s ⟨hc, hi, he⟩ => ⟨hc, ⟨hi, he⟩, hsl σ _ hi.1⟩) fun _ _ h => h) ?_
  -- The padding.
  refine VP.seq ((pad_vp h hg hnb hnb0 hfit (Inv := fun σ m => Inv σ m ∧ h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨hi, he⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp) σ m m' hi hf,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)).trans he⟩)
    (fun σ m hi => hsn σ m hi.1)).mono
      (fun σ s ⟨hc, ⟨⟨hi, hy⟩, he⟩, lb, sl', slb⟩ => ⟨hc, ⟨hi, he⟩, lb, sl', slb, hy⟩) fun _ _ h => h) ?_
  -- Every block compressed.
  refine VP.seq ((compLoop_vp h hg hnb hnb0 (lb := fun σ => ((msg σ).length + h.L) / h.B)
    (yv := fun σ i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) hq
    (Inv := fun σ m => Inv σ m ∧ m.readW (L.fr sLb) 32 = BitVec.ofNat 32 (((msg σ).length + h.L) / h.B))
    (fun σ m m' ⟨hi, hb⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) σ m m' hi hf,
      slot_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact sl sLb (by decide) (by pomega)
        · exact sl sLb (by decide) (by pomega)
        · exact sl sLb (by decide) (by pomega)
        · exact Lay.fr_sep (by decide) (by decide) (by decide)
        · exact Lay.fr_low (by decide) hC) hb⟩)
    (fun σ m hi => hi.2) (fun σ m hi => hsn σ m hi.1)).mono
      (fun σ s ⟨hc, ⟨hi, he⟩, _, _, slb, hy⟩ => ⟨hc, ⟨hi, slb⟩, hy, he⟩) fun _ _ h => h) ?_
  -- The digest.
  refine (out_vp h hg (X := fun σ m => (Inv σ m ∧ m.readW (L.fr sLb) 32 =
      BitVec.ofNat 32 (((msg σ).length + h.L) / h.B)) ∧ h.md.stateAt m (sa scr oSel) =
      h.md.compressList h.ok.iv (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1))).mono (fun _ _ h => h) fun σ s ⟨hc, m₀, ⟨⟨hi, _⟩, he⟩, hf, hm⟩ => ?_
  refine ⟨hc, hIs _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp) σ _ _ hi hf, fun i hi => ?_⟩
  have hl := h.md.digest_length (h.md.stateAt m₀ (sa scr oSel))
  rw [hm, sa_writeBytes scr m₀ (by omega) (by pomega), he, h.ok.link.hash]
  have hq1 : ((msg σ).length + h.L) / h.B + 1 ≤ nbm := hq σ
  have key : h.md.compressList h.ok.iv
      (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1) =
      h.md.compressList h.ok.iv (h.md.pad (msg σ)) ((h.md.pad (msg σ)).length / h.B) := by
    rw [RsaPss.pad_length h.md _ hB0 hLB, Nat.mul_div_cancel_left _ hB0]
    refine h.md.compressList_congr fun j hj => ?_
    have hT : j < nbm * h.B := by
      have := Nat.mul_le_mul_left h.B hq1
      rw [Nat.mul_comm h.B nbm] at this
      omega
    rw [ylist_getD hT, padY_eq hB0 hLB _ _ hj, RsaPss.pad_getD h.md _ hB0 hLB hj]
  rw [key, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rfl

end VG.Proof.RsaPss.X86
