module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Whole
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.RestTag
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs the whole blocks,
if any (`wholeIte_ok`), and the rest, if any (`restIte_ok`): for `seal`
`OCB-ENCRYPT`'s ciphertext, offset and checksum (`bodySeal_ok`), for `open`
`OCB-DECRYPT`'s (`bodyOpen_ok`). As on AArch64
(`Proof/AesOcb/AArch64/Body.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (eval_zero and15 shr4 ofNat_sub64 Keeps)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_lsr → cwp_lsr, wp_li → cwp_li, wp_and → cwp_and,
  wp_sub → cwp_sub, wp_add → cwp_add

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 l : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (V .r27 + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem (V .r29) (16 * (R + 1)))
        (blockAtMem s.mem (V .r27 + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block []) (whole (.call name c) pre post))) s
      (WholePost V sp (V .r27) (n / 16) O0 l
        (fun k => G (bytesAt s.mem (V .r29) (16 * (R + 1)))
          (blockAtMem s.mem (V .r27 + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  refine WP.seq (cwp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have r3₁ : s₁.gpr .r3 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, E.r23, h23, shr4 hn]
  have E₁ : Env V sp s₁ := E.others (rs := [.r3]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr
  refine WP.ite _ (eval_zero r3₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [u₁.mem]; exact Frame.refl _ _, u₁.rd, u₁.wr, fun k hk => absurd hk (by omega),
      by rw [u₁.mem, hofs, hm]; rfl, by rw [u₁.mem, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    have hD₁ := hD.of_eq u₁.rd u₁.wr
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 L E₁ hR h28 h23 hD₁ (by omega)
      (by rw [u₁.mem, hofs]) (by rw [u₁.mem, ho0]) (by rw [u₁.mem, hck]) (by rw [u₁.mem, hl0])
      (fun i => by rw [u₁.mem, hckF1]) hckF2₀ (fun i => by rw [u₁.mem, hckF2])) fun t P => ?_
    refine ⟨P.env, by have f := P.frame; rwa [u₁.mem] at f, by rw [P.rd, u₁.rd], by rw [P.wr, u₁.wr],
      fun k hk => by rw [P.blk k hk, u₁.mem], P.ofs, by rw [P.ck]⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {V : Reg → BitVec 64} {sp : Addr} {t : State} (E : Env V sp t) {n : Nat} (hn : n < 2 ^ 64)
    (h23 : V .r23 = BitVec.ofNat 64 n) :
    WP isa (.block [.li .r0 15, .logic .and .r25 .r23 .r0, .sub .r24 .r23 .r25, .add .r24 .r24 .r27]) t fun t₁ =>
      t₁.gpr .r24 = V .r27 + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .r25 = BitVec.ofNat 64 (n % 16) ∧
      (∀ r, r ∉ [.r0, .r24, .r25] → t₁.gpr r = t.gpr r) ∧ Keeps t t₁ := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine cwp_li (by decide) fun t₁ u₁ => cwp_and fun t₂ u₂ => cwp_sub fun t₃ u₃ => cwp_add fun t₄ u₄ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.lr, u₃.lr, u₂.lr, u₁.lr]⟩⟩
  · have r25₂ : t₂.gpr .r25 = BitVec.ofNat 64 (n % 16) := by
      rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), E.r23, h23, and15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    have r24₃ : t₃.gpr .r24 = BitVec.ofNat 64 (16 * (n / 16)) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r23, h23, r25₂, hsub]
    rw [u₄.gpr, r24₃, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.r27,
      BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), E.r23, h23, and15,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.2.1, u₂.other _ hr.2.2, u₁.other _ hr.1]

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) :
    Prop where
  env : Env V sp t'
  frame : Frame [⟨V .r31 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .r31 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .r31 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .r29)
    else blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (V .r29) R
        (blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .r29))))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (V .r31 + BitVec.ofNat 64 ckO) =
    if 0 < r then
      blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) t (V .r27) n) :
    WP isa (.seq (.block [.li .r0 15, .logic .and .r25 .r23 .r0, .sub .r24 .r23 .r25, .add .r24 .r24 .r27])
        (.ite (.zero .d .r25) (.block []) (rest enc))) t
      (TailPost enc V sp R (V .r27 + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  refine WP.seq (WP.mono (bodyTail_ok E hn h23) fun t₁ ⟨r24₁, r25₁, g₁, k₁⟩ => ?_)
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.ite _ (eval_zero r25₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [k₁.mem]; exact Frame.refl _ _, k₁.rd, k₁.wr, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, k₁.mem]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : DBuf (V .r29) (V .r31) t₁ (V .r27 + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq k₁.rd k₁.wr
    refine WP.mono (rest_ok enc L E₁ hR h28 hr (Nat.mod_lt _ (by decide)) r24₁ r25₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← k₁.mem]; exact P.frame, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, k₁.mem]
    · rw [P.out, k₁.mem]
    · rw [P.ck, k₁.mem]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 256, 16⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (V : Reg → BitVec 64) (sp D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) :
    Prop where
  env : Env V sp t
  frame : Frame (bodyR (V .r31) D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (V .r31 + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, decG_eq]; rfl

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Offset.sub W (by decide)
      (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (body true) s (BodyPost V sp (V .r27) n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .r29) R (offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29)
       else offAt O0 (ctxLstar s.mem (V .r29)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (V .r27) n) (n / 16) ^^^ pad ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (V .r27) n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .r29) (V .r31) s (V .r27) (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .r29) (V .r31) s ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨(V .r27), 16 * (n / 16)⟩ : Region).Disjoint ⟨(V .r27) + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint (V .r27) (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem (V .r27) n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem (V .r27) (by omega)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29))
    (ckF1 := ckOf fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames hcall_enc sealPre_ok xorOfs_ok L E hR h28 h23 hD
    hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .r31) (V .r27) (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok true L Pw.env hR h28 h23 (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .r29) R = ctxCiph s.mem (V .r29) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .r29) = ctxLstar s.mem (V .r29) :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem (V .r27) n).drop (16 * (n / 16)) = bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem (V .r27) hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem ((V .r31) + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem (V .r27) (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem (V .r27) (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- `body` for `open`. -/
theorem bodyOpen_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (body false) s (BodyPost V sp (V .r27) n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .r29) R (offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29))))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29)
       else offAt O0 (ctxLstar s.mem (V .r29)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (V .r27) n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .r29) R (offAt O0 (ctxLstar s.mem (V .r29)) (n / 16) ^^^ ctxLstar s.mem (V .r29)))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .r29) (V .r31) s (V .r27) (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .r29) (V .r31) s ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨(V .r27), 16 * (n / 16)⟩ : Region).Disjoint ⟨(V .r27) + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint (V .r27) (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem (V .r27) n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem (V .r27) (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .r29) (16 * (R + 1)))
      (blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .r29)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .r29)) (i + 1))
    Proof.Aes.PPC64LE.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok openPost_ok L E hR h28 h23 hD
    hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .r31) (V .r27) (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok false L Pw.env hR h28 h23 (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .r29) R = ctxCiph s.mem (V .r29) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .r29) = ctxLstar s.mem (V .r29) :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem (V .r27) n).drop (16 * (n / 16)) = bytesAt s.mem ((V .r27) + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem (V .r27) hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem ((V .r31) + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem (V .r27) (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .r29) R) O0 (ctxLstar s.mem (V .r29)) (bytesAt s.mem (V .r27) n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem (V .r27) (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.PPC64LE
