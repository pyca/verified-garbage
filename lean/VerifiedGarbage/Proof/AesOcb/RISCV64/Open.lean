module

-- separate module: its proofs (about 2 s) build in parallel with the constant-time ones, `FrontCT` and `FnCT`

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
import VerifiedGarbage.Proof.AesOcb.RISCV64.CmpMask
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-OCB on RISC-V: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front` with the
tag at `W + t2O`, then the received tag padded at `W` (`recv`), the
comparison of the padded tags (`cmp`), the mask of the data (`mask`, which
loads the data's address from its slot) and `restore`, which keeps the
result in `a0` (`open_wp`). As on PPC64LE (`Proof/AesOcb/PPC64LE/Open.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (covers_mem covers_left SavedAt)

/-- Two padded tags are equal iff the tags are. -/
theorem padded_eq {xs ys : List Byte} {t : Nat} (hx : xs.length = t) (hy : ys.length = t) :
    xs ++ zeros (16 - t) = ys ++ zeros (16 - t) ↔ xs = ys := by
  constructor
  · intro h; exact (List.append_inj h (by rw [hx, hy])).1
  · intro h; rw [h]

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' {s₀ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (hW : stackArg s₀ 2 = W)
    (hT : stackArg s₀ 0 = T) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (ha0 : s₀.gpr .a0 = K) (ha1 : s₀.gpr .a1 = BitVec.ofNat 64 R) (ha2 : s₀.gpr .a2 = N)
    (ha3 : s₀.gpr .a3 = BitVec.ofNat 64 nl) (ha4 : s₀.gpr .a4 = A) (ha5 : s₀.gpr .a5 = BitVec.ofNat 64 al)
    (ha6 : s₀.gpr .a6 = D) (ha7 : s₀.gpr .a7 = BitVec.ofNat 64 n) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s₀.mem K R) (Spec.Ocb.ctxInv s₀.mem K R) (ctxLstar s₀.mem K) tl
          (bytesAt s₀.mem N nl) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) (bytesAt s₀.mem T tl) with
      | some pt => (s'.gpr .a0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .a0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L₀ : Lay (s₀.gpr .a0) W := by rw [ha0]; exact Ar.lay
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := by rw [ha0]; exact Ar.perm.k
  have hn := Ar.data.lt
  unfold «open» front
  refine WP.seq (WP.seq (WP.mono (entry_ok L₀ Ar.perm.w hC Ar.sa hW hT Ar.args Ar.argsW) fun s₁ P₁ => ?_))
  have hW₁ : s₁.gpr .s0 = W := P₁.s0
  have hK₁ : s₁.gpr .s2 = K := P₁.s2.trans ha0
  have hs3 : s₁.gpr .s3 = BitVec.ofNat 64 R := P₁.s3.trans ha1
  have h11 : s₁.gpr .s11 = BitVec.ofNat 64 n := P₁.s11.trans ha7
  have L : Lay (s₁.gpr .s2) (s₁.gpr .s0) := by rw [hK₁, hW₁]; exact Ar.lay
  have hal : (s₁.gpr .s0).toNat % 8 = 0 := L.wal
  refine WP.assoc (WP.seq (WP.mono (preRest_wp Ar P₁ htl ha0 ha1 ha2 ha3 ha4 ha5 ha6) fun s₃ P₃ => ?_))
  have hD₃ : DBuf (s₁.gpr .s2) (s₁.gpr .s0) s₃ D n := by
    rw [hK₁, hW₁]; exact Ar.data.of_eq P₃.rd P₃.wr
  have c₃ : ctxCiph s₃.mem K R = ctxCiph s₀.mem K R := ctxCiph_W Ar.lay P₃.frame Ar.rounds
  have i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s₀.mem K R := ctxInv_W Ar.lay P₃.frame Ar.rounds
  have l₃ : ctxLstar s₃.mem K = ctxLstar s₀.mem K := ctxLstar_W Ar.lay P₃.frame
  have d₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodyOpen_ok L P₃.env Ar.rounds hs3 h11 (by rw [hW₁]; exact P₃.slots.data) hD₃
    (O0 := Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)) (by rw [hW₁]; exact P₃.ofs)
    (by rw [hW₁]; exact P₃.o0) (by rw [hW₁]; exact P₃.ck) (by rw [hW₁, hK₁, P₃.l0, l₃])) fun s₄ B => ?_)
  have Bf : Frame (bodyR W D n) s₃.mem s₄.mem := by have := B.frame; rwa [hW₁] at this
  have F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut Bf
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s₀.mem K R := (ctxCiph_mut Ar.lay Ar.data.k F₄ Ar.rounds).trans c₃
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (tag_ok L B.env Ar.rounds hs3 (.inr rfl)) fun s₅ T₅ => ?_
  have Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
      s₄.mem s₅.mem := by have := T₅.frame; rwa [hW₁] at this
  have F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (.inr ⟨by decide, by decide⟩) Tf
  have sv₅ := saved_mut Ar.lay Ar.data.w (saved_mut Ar.lay Ar.data.w P₃.saved F₄) F₅
  have S₅ : Slots W A D s₅.mem := Slots.mut Ar.lay Ar.data.w F₅ (Slots.mut Ar.lay Ar.data.w F₄ P₃.slots)
  have E₅ := T₅.env
  have rd₅ : s₅.rd = s₀.rd := by rw [T₅.rd, B.rd, P₃.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [T₅.wr, B.wr, P₃.wr]
  -- The received tag, to `W`.
  have hTd : (⟨s₁.gpr .s9, tl⟩ : Region).Disjoint ⟨s₁.gpr .s0, 2560⟩ := by rw [P₁.s9, hW₁]; exact Ar.tag.w
  refine WP.seq (WP.mono (recv_ok E₅ hal (P₁.s8.trans htl) Ar.t1 Ar.t16
    (by rw [P₁.s9, rd₅, wr₅]; exact Ar.tag.rd) hTd) fun s₆ ⟨b₆, f₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ := E₅.others g₆ sp₆ rd₆ wr₆
  rw [hW₁, P₁.s9] at b₆
  rw [hW₁] at f₆
  have F₆ : Frame (mutR W D n) s₅.mem s₆.mem :=
    f₆.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₆ hal (P₁.s8.trans htl) Ar.t1 Ar.t16) fun s₇ ⟨a0₇, f₇, g₇, sp₇, rd₇, wr₇⟩ => ?_)
  have E₇ := E₆.others g₇ sp₇ rd₇ wr₇
  rw [hW₁] at a0₇ f₇
  have F₇ : Frame (mutR W D n) s₆.mem s₇.mem :=
    f₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide)
  let c : Bool := decide (bytesAt s₆.mem (W + BitVec.ofNat 64 tagO) 16 =
    bytesAt s₆.mem (W + BitVec.ofNat 64 t2O) tl ++ zeros (16 - tl))
  have a0c : s₇.gpr .a0 = if c then 1 else 0 := by
    rw [a0₇]; simp only [c, decide_eq_true_eq]
  have hD₇ : DBuf (s₁.gpr .s2) (s₁.gpr .s0) s₇ D n := by
    rw [hK₁, hW₁]; exact Ar.data.of_eq (by rw [rd₇, rd₆, rd₅]) (by rw [wr₇, wr₆, wr₅])
  have S₇ : Slots (s₁.gpr .s0) A D s₇.mem := by
    rw [hW₁]; exact Slots.mut Ar.lay Ar.data.w F₇ (Slots.mut Ar.lay Ar.data.w F₆ S₅)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₇ hal S₇ h11 hD₇ a0c) fun s₈ ⟨m₈, g₈, sp₈, rd₈, wr₈⟩ => ?_)
  have E₈ := E₇.others g₈ sp₈ rd₈ wr₈
  have F₈ : Frame [⟨D, n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have F₅₈ : Frame (mutR W D n) s₅.mem s₈.mem :=
    (F₆.trans F₇).trans (F₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutD fun _ h => h)
  have sv₈ : SavedAt s₈.mem W s₀ := saved_mut Ar.lay Ar.data.w sv₅ F₅₈
  -- `restore`.
  refine WP.mono (Proof.AesGcm.RISCV64.restore_ok (E₈.s0.trans hW₁) Ar.lay.wal
    (by rw [rd₈, wr₈, rd₇, wr₇, rd₆, wr₆, rd₅, wr₅]; exact covers_left Ar.perm.w) sv₈
    (by rw [E₈.sp])) fun s₉ ⟨abi, m₉, a0₉, _, _⟩ => ⟨abi, ?_⟩
  -- The plaintext and the comparison.
  have a0₉' : s₉.gpr .a0 = if c then 1 else 0 := by
    rw [a0₉, g₈ _ (by decide), a0c]
  have hout := B.out
  rw [hK₁, c₃, i₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [hW₁, hK₁, l₃] at hofs
  have hck := B.ck
  rw [hW₁, hK₁, c₃, i₃, l₃, d₃] at hck
  have hTn := Ar.tag.lt
  have Ff : Frame [⟨W, 2560⟩, ⟨D, n⟩] s₀.mem s₅.mem :=
    (P₃.frame.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans ((F₄.trans F₅).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  have recv : bytesAt s₅.mem T tl = bytesAt s₀.mem T tl :=
    Proof.Cmac.bytesAt_frame Ff (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Ar.tag.w
      · exact Ar.td) (by omega)
  have t2₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inr (by simp only [tagO, t2O]; omega))
        (by have := Ar.t16; simp only [t2O]; omega) (by decide)) (by omega)
  have tagv := T₅.val
  rw [hW₁, hK₁, hck, hofs, ld₄, sum₄, cK₄] at tagv
  have d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
    have d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
      rw [Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega),
        Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega),
        Proof.Cmac.bytesAt_frame Tf (tag_data Ar.data.w (by decide)) (by omega)]
    rw [m₉, m₈, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) hn, length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₇]
  rw [a0₉', d₉, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  have hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s₀.mem T tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [decide_eq_true_iff, b₆, t2₆, recv, hx,
      padded_eq (length_bytesAt _ _ _) (by rw [List.length_take, Proof.Ocb.toBytes_length]; have := Ar.t16; omega),
      eq_comm]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp {s : State} (h : openRISCV64.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp' (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.RISCV64
