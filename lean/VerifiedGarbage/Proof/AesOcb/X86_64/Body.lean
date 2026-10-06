import VerifiedGarbage.Proof.AesOcb.X86_64.Whole
import VerifiedGarbage.Proof.AesOcb.X86_64.RestTag

/-!
# AES-OCB on x86-64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs `whole` on the
`m = len / 16` whole blocks if there are any (`wholeIte_ok`), then `rest` on
the `len mod 16` bytes after them if there are any (`restIte_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e length_bytesAt bytesAt_frame)

/-- The number of whole blocks, in `r13`. -/
theorem bodyHead_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {n : Nat} (hn : n < 2 ^ 64)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ s₁, runBlock isa [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)] s = some s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .r13 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  refine ⟨_, by orun [E.r15, r₁, hlen], ?_, ?_, ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn,
      Proof.AesCcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega)]
  · rfl
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h, ite_false]
  all_goals rfl

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) {O0 l : Block}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hT : TblL W l n s.mem)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s
      (WholePost K W SP D (16 * (n / 16)) (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyHead_ok E hn hlen
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, fun k hk => absurd hk (by omega),
      by rw [m₁, hofs, hm]; rfl, by rw [m₁, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    rw [← m₁]
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nosp depth hcall hB1 hB2 L E₁ hR (hD.take' (Nat.mul_div_le n 16) |>.of_eq rd₁ wr₁)
      (Nat.le_refl _) (by omega) (by rw [m₁]; exact hdata) r13₁ (by rw [m₁]; exact hrnd)
      (by rw [m₁]; exact hofs) (by rw [m₁]; exact ho0) (by rw [m₁]; exact hck) (by rw [m₁]; exact hT)
      (fun i => by rw [m₁]; exact hckF1 i) hckF2₀ (fun i => by rw [m₁]; exact hckF2 i)) fun t P => ?_
    exact ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {D : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ t₁, runBlock isa [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)] t = some t₁ ∧
      t₁.gpr .rbx = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (n % 16) ∧
      t₁.zf = some (decide (n % 16 = 0)) ∧ t₁.mem = t.mem ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8 := E.perm.wR (by decide)
  have r₂ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  simp only [dataO] at hdata
  have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesCcm.X86_64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine ⟨_, by orun [E.r15, r₁, r₂, hdata, hlen], ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      toNat_ofNat_of_lt hn, hsub]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      toNat_ofNat_of_lt hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15,
      Proof.AesCcm.X86_64.and15', toNat_ofNat_of_lt hn,
      Proof.AesCcm.X86_64.and_self_beq (show n % 16 < 2 ^ 64 by omega)]
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, ite_false]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W SP : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP t D n)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (rest (callees v) enc))) t
      (TailPost enc K W SP R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, rbx₁, r12₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok E hn hdata hlen
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : DBuf K W SP t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq rd₁ wr₁
    refine WP.mono (rest_ok v enc L E₁ hR (by rw [m₁]; exact hrnd) hr (Nat.mod_lt _ (by decide)) rbx₁ r12₁ hP)
      fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 48⟩, wC W, below SP 8, ⟨D, n⟩]

theorem bodyR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W SP D n) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (K W SP D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env K W SP t
  frame : Frame (bodyR W SP D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ck

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

/-- A buffer apart from `W`, the stack and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W SP Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hs : (below SP 8).Disjoint ⟨Q, k⟩) (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm
  · exact hp

/-- A buffer apart from `W`, the stack and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W SP Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hs : (below SP 8).Disjoint ⟨Q, k⟩) (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W SP D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm
  · exact hp

theorem wholeR_sub {W SP D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W SP D k, ∃ r' ∈ bodyR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W SP D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W SP D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hT : TblL W (ctxLstar s.mem K) n s.mem) :
    WP isa (body (callees v) true) s (BodyPost K W SP D n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W SP s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W SP s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, ↓reduceIte]
  refine wp_seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K)
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    v.encOk v.encNosp v.encDepth hcall_enc sealPre_ok xorOfs_ok L E hR hD hdata hlen hrnd hofs ho0 hck hT
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W SP D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hrnd₁ := (kept_read L hDm.w fW (d := 232) (by decide)).trans hrnd
  have hdata₁ := (kept_read L hDm.w fW (d := 208) (by decide)).trans hdata
  have hlen₁ := (kept_read L hDm.w fW (d := 216) (by decide)).trans hlen
  refine WP.mono (restIte_ok v true L Pw.env hR hrnd₁ (hD.of_eq Pw.rd Pw.wr) hdata₁ hlen₁) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    bytesAt_frame Pw.frame (disj_whole hP.w hP.stk dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [bytesAt_frame Pt.frame (disj_tail hDm.w hDm.stk dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
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
theorem bodyOpen_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hT : TblL W (ctxLstar s.mem K) n s.mem) :
    WP isa (body (callees v) false) s (BodyPost K W SP D n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W SP s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W SP s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine wp_seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem K (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem K) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem K) (i + 1))
    v.decOk v.decNosp v.decDepth hcall_dec xorOfs_ok openPost_ok L E hR hD hdata hlen hrnd hofs ho0 hck hT
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W SP D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  have hrnd₁ := (kept_read L hDm.w fW (d := 232) (by decide)).trans hrnd
  have hdata₁ := (kept_read L hDm.w fW (d := 208) (by decide)).trans hdata
  have hlen₁ := (kept_read L hDm.w fW (d := 216) (by decide)).trans hlen
  refine WP.mono (restIte_ok v false L Pw.env hR hrnd₁ (hD.of_eq Pw.rd Pw.wr) hdata₁ hlen₁) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    bytesAt_frame Pw.frame (disj_whole hP.w hP.stk dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [bytesAt_frame Pt.frame (disj_tail hDm.w hDm.stk dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
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
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.X86_64
