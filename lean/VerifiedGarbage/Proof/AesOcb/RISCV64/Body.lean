module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Whole
import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.RISCV64.Nonce
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env

/-!
# AES-OCB on RISC-V: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs the whole blocks,
if any (`wholeIte_ok`), and the rest, if any (`restIte_ok`): for `seal`
`OCB-ENCRYPT`'s ciphertext, offset and checksum (`bodySeal_ok`), for `open`
`OCB-DECRYPT`'s (`bodyOpen_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/Body.lean`), but the data's address is in its slot in
`W` (`Slots`), from which the whole blocks and the rest load it.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (and15 shr4 ofNat_sub64 Keeps)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : Prog isa} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    {V : Reg → BitVec 64} {sp : Addr}
    (hB1 : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk (V .s0) post (fun b o => b ^^^ o) fC2)
    (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 l : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem (V .s2) (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block []) (whole (.call name c) pre post))) s
      (WholePost V sp D (n / 16) O0 l
        (fun k => G (bytesAt s.mem (V .s2) (16 * (R + 1)))
          (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have t1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (n / 16) := by rw [u₁.gpr, E.s11, h11, shr4 hn]
  have E₁ : Env V sp s₁ := E.others (rs := [.t1]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr
  refine WP.ite _ (eval_zero t1₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [u₁.mem]; exact Frame.refl _ _, u₁.rd, u₁.wr, fun k hk => absurd hk (by omega),
      by rw [u₁.mem, hofs, hm]; rfl, by rw [u₁.mem, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    have hD₁ := hD.of_eq u₁.rd u₁.wr
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 L E₁ hR hs3 h11 (by rw [u₁.mem, hS]) hD₁
      (by omega) (by rw [u₁.mem, hofs]) (by rw [u₁.mem, ho0]) (by rw [u₁.mem, hck]) (by rw [u₁.mem, hl0])
      (fun i => by rw [u₁.mem, hckF1]) hckF2₀ (fun i => by rw [u₁.mem, hckF2])) fun t P => ?_
    refine ⟨P.env, by have f := P.frame; rwa [u₁.mem] at f, by rw [P.rd, u₁.rd], by rw [P.wr, u₁.wr],
      fun k hk => by rw [P.blk k hk, u₁.mem], P.ofs, by rw [P.ck]⟩

theorem andi15 (x : BitVec 64) : x &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 (x.toNat % 16) := and15 x

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {V : Reg → BitVec 64} {sp : Addr} {K : Addr} (L : Lay K (V .s0)) {t : State} (E : Env V sp t)
    {n : Nat} (hn : n < 2 ^ 64) (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) :
    WP isa (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO, .add .s4 .s4 .t1]) t
      fun t₁ => t₁.gpr .s4 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .s5 = BitVec.ofNat 64 (n % 16) ∧
        (∀ r, r ∉ [.t1, .s4, .s5] → t₁.gpr r = t.gpr r) ∧ Keeps t t₁ := by
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine wp_andi (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => ?_
  have s5₁ : t₁.gpr .s5 = BitVec.ofNat 64 (n % 16) := by
    rw [u₁.gpr, E.s11, h11, andi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have s4₂ : t₂.gpr .s4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [u₂.gpr, u₁.other _ (by decide), E.s11, h11, s5₁, hsub]
  refine wp_ld (a := V .s0 + BitVec.ofNat 64 dataO) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s0]) (L.alW (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun t₃ u₃ => wp_add fun t₄ u₄ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩⟩
  · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), s4₂, u₂.mem, u₁.mem, hS, BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), s5₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.1, u₁.other _ hr.2.2]

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) :
    Prop where
  env : Env V sp t'
  frame : Frame [⟨V .s0 + BitVec.ofNat 64 ofsO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨V .s0 + BitVec.ofNat 64 t2O, 16⟩, ⟨V .s0 + BitVec.ofNat 64 ckO, 16⟩, ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩,
    ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .s2)
    else blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (V .s2) R
        (blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (V .s2))))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (V .s0 + BitVec.ofNat 64 ckO) =
    if 0 < r then
      blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {t : State}
    (E : Env V sp t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) t D n) :
    WP isa (.seq (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO, .add .s4 .s4 .t1])
        (.ite (.zero .s5) (.block []) (rest enc))) t
      (TailPost enc V sp R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  refine WP.seq (WP.mono (bodyTail_ok L E hn h11 hS) fun t₁ ⟨s4₁, s5₁, g₁, k₁⟩ => ?_)
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.ite _ (eval_zero s5₁ (by omega)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [k₁.mem]; exact Frame.refl _ _, k₁.rd, k₁.wr, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, k₁.mem]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : DBuf (V .s2) (V .s0) t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq k₁.rd k₁.wr
    refine WP.mono (rest_ok enc L E₁ hR hs3 hr (Nat.mod_lt _ (by decide)) s4₁ s5₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← k₁.mem]; exact P.frame, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, k₁.mem]
    · rw [P.out, k₁.mem]
    · rw [P.ck, k₁.mem]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called and the data. -/
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
structure BodyOut (V : Reg → BitVec 64) (sp D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) :
    Prop where
  env : Env V sp t
  frame : Frame (bodyR (V .s0) D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = ck

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
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
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
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (body true) s (BodyOut V sp D n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)
       else offAt O0 (ctxLstar s.mem (V .s2)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .s2) (V .s0) s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .s2) (V .s0) s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2))
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames hcall_enc (sealPre_ok L.wal) xorOfs_ok L E hR hs3
    h11 hS hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .s0) D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hSt : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w Pw.frame, hS]
  refine WP.mono (restIte_ok true L Pw.env hR hs3 h11 hSt (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .s2) R = ctxCiph s.mem (V .s2) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .s2) = ctxLstar s.mem (V .s2) := ctxLstar_mut L hDm.k fW
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks,
      Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- `body` for `open`. -/
theorem bodyOpen_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (body false) s (BodyOut V sp D n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2))))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)
       else offAt O0 (ctxLstar s.mem (V .s2)) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (V .s2) R (offAt O0 (ctxLstar s.mem (V .s2)) (n / 16) ^^^ ctxLstar s.mem (V .s2)))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf (V .s2) (V .s0) s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf (V .s2) (V .s0) s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .s2) (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .s2)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .s2)) (i + 1))
    Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok (openPost_ok L.wal) L E hR hs3
    h11 hS hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR (V .s0) D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hSt : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w Pw.frame, hS]
  refine WP.mono (restIte_ok false L Pw.env hR hs3 h11 hSt (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  have cT : ctxCiph t.mem (V .s2) R = ctxCiph s.mem (V .s2) R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem (V .s2) = ctxLstar s.mem (V .s2) := ctxLstar_mut L hDm.k fW
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (V .s0 + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem (V .s2) R) O0 (ctxLstar s.mem (V .s2)) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega), Proof.Ocb.bytesAt_blocks,
      Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.RISCV64
