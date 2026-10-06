import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt

/-!
# AES-GCM on x86-64: the text of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. `streamText enc` takes the
`n` bytes at `D` in pieces, keeping `SInv` between them: the first `j`
bytes are done (encrypted or decrypted, and their ciphertext absorbed), the
rest are as they were. The pieces: the additional data padded if there is
no text yet (`start_ok`), the head (`sHead_ok`, then `part_ok`), the whole
blocks in one call (`blocks_ok`), and the rest (`part_ok`): `streamText_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- What `streamText` writes. -/
abbrev stFrame (St W SP D : Addr) (n : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 64⟩, ⟨D, n⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 192, 32⟩,
    ⟨W + BitVec.ofNat 64 448, 2112⟩, below SP 24]

/-- The ciphertext of the text `x` from byte `P` on: `x` encrypted, if `enc`,
or `x`. -/
def ctext (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) (x : List Byte) : List Byte :=
  if enc then xorKs ciph icb P x else x

theorem ctext_append (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) (x y : List Byte) :
    ctext enc ciph icb P (x ++ y) = ctext enc ciph icb P x ++ ctext enc ciph icb (P + x.length) y := by
  cases enc
  · rfl
  · exact Proof.Gcm.xorKs_append _ _ _ _ _

theorem length_ctext (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) (x : List Byte) :
    (ctext enc ciph icb P x).length = x.length := by
  cases enc
  · rfl
  · exact Proof.Gcm.length_xorKs _ _ _ _

theorem ctext_nil (enc : Bool) (ciph : Block → Block) (icb : Block) (P : Nat) : ctext enc ciph icb P [] = [] := by
  cases enc <;> rfl

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

/-- Equal bytes, split. -/
theorem bytesAt_split_eq {m m' : Mem} {p : Addr} {a b : Nat} (h : bytesAt m p (a + b) = bytesAt m' p (a + b)) :
    bytesAt m p a = bytesAt m' p a ∧ bytesAt m (p + BitVec.ofNat 64 a) b = bytesAt m' (p + BitVec.ofNat 64 a) b := by
  rw [bytesAt_add, bytesAt_add] at h
  exact List.append_inj h (by rw [length_bytesAt, length_bytesAt])

/-- What stays the same through `streamText`: the layout and what the call
of the whole blocks needs, the rounds and the hash subkey. -/
structure SCtx (M : Gcm.X86_64.Stitch.CtxMode) (Ctx St W SP : Addr) (R : Nat) (H : Block) (D : Addr) (n : Nat)
    (m₀ : Mem) : Prop where
  lay : Lay Ctx St W SP
  rounds : RoundsAt m₀ W R
  hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H
  t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩
  t_s : (below SP 24).Disjoint ⟨St, 80⟩
  t_w : (below SP 24).Disjoint ⟨W, 2560⟩
  t_d : (below SP 24).Disjoint ⟨D, n⟩
  sp24 : 24 ≤ SP.toNat
  /-- The key context, of kind `M`. -/
  xw : Ctx.toNat + M.len ≤ 2 ^ 64
  xs : (⟨Ctx, M.len⟩ : Region).Disjoint ⟨St, 80⟩
  xw' : (⟨Ctx, M.len⟩ : Region).Disjoint ⟨W, 2560⟩
  xd : (⟨Ctx, M.len⟩ : Region).Disjoint ⟨D, n⟩
  xt : (below SP 24).Disjoint ⟨Ctx, M.len⟩
  xok : M.ok m₀ Ctx

/-- Between the pieces of `streamText`: the first `j` of the `n` bytes at
`D` done, from `m₀`. Given `Hyp` (the streaming state at the start, with
`x₀` absorbed and `P₀` bytes of text so far), GHASH has absorbed their
ciphertext and the counter is past them. -/
structure SInv (M : Gcm.X86_64.Stitch.CtxMode) (Hyp : Prop) (Ctx St W SP : Addr) (R : Nat) (H icb : Block) (x₀ : List Byte) (P₀ : Nat)
    (enc : Bool) (D : Addr) (n : Nat) (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW Ctx St W SP s D n
  le : j ≤ n
  frame : Frame (stFrame St W SP D n) m₀ s.mem
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  abs : Hyp → Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
    (x₀ ++ ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
  ctr : Hyp → Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P₀ + j)
  out : Hyp → bytesAt s.mem D j = xorKs (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)
  cov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem ctx_stFrame {D : Addr} {n : Nat} (hC : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) : ∀ r ∈ stFrame St W SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact hC
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact t_c.symm

/-- The slots of `W` below `192` are outside `stFrame`. -/
theorem w_stFrame {D : Addr} {n d k : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) (h₁ : 128 ≤ d) (h₂ : d + k ≤ 192) :
    ∀ r ∈ stFrame St W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

/-- `J₀` is outside `stFrame`. -/
theorem j0_stFrame {D : Addr} {n : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩)
    (t_s : (below SP 24).Disjoint ⟨St, 80⟩) : ∀ r ∈ stFrame St W SP D n, (⟨St, 16⟩ : Region).Disjoint r := by
  intro r hr
  have e : (⟨St, 16⟩ : Region) = ⟨St + BitVec.ofNat 64 0, 16⟩ := by rw [BitVec.add_zero]
  rw [e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.st_st (.inl (by decide)) (by decide) (by decide)
  · exact (hD.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (t_s.sub_right (Lay.stSub (by decide))).symm

omit L in
/-- The return address is outside `stFrame`. -/
theorem ret_stFrame {D : Addr} {n : Nat} (rS : (⟨SP, 8⟩ : Region).Disjoint ⟨St, 80⟩)
    (rD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) (rW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ stFrame St W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rS.sub_right (Lay.stSub (by decide))
  · exact rD
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact rW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (n := 24) (k := 8) (by decide)

omit L in
/-- `crypt` over part of the data writes within `stFrame`. -/
theorem crFrame_st {D : Addr} {n j k : Nat} (hk : j + k ≤ n) {m m' : Mem}
    (hf : Frame (crFrame St W SP (D + BitVec.ofNat 64 j) k) m m') : Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D hk⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

omit L in
theorem absFrame_st {D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (absFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

omit L in
theorem tFrame_st {D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (tFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

omit L in
theorem obFrame_st {D : Addr} {n j q : Nat} (hk : j + q * 16 ≤ n) {m m' : Mem}
    (hf : Frame (obFrame St W SP (D + BitVec.ofNat 64 j) q) m m') : Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D hk⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

omit L in
theorem slots_st {D : Addr} {n d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) {m m' : Mem}
    (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') : Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ h₁ (by omega)⟩

omit L in
/-- The accumulator and the buffer, through a frame apart from them. -/
theorem abs_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r) {H : Block} {x : List Byte}
    (h : Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x) :
    Absorbed m' (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H x := by
  have hl := Nat.mod_lt x.length (show 16 > 0 by decide)
  exact h.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))
    (bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by omega))) (by omega))

omit L in
/-- The counter and the keystream block, through a frame apart from them. -/
theorem ctr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r) {ciph : Block → Block} {icb : Block}
    {P : Nat} (h : Ctr m (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb P) :
    Ctr m' (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) ciph icb P :=
  h.congr (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))
    (blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide)))

omit L in
/-- The rest of the data, after more of it is done. -/
theorem rest_step {D : Addr} {n j k : Nat} (hk : j + k ≤ n) (hn : n < 2 ^ 64) {m₀ m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨D + BitVec.ofNat 64 (j + k), n - (j + k)⟩ : Region).Disjoint r)
    (h : bytesAt m (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) :
    bytesAt m' (D + BitVec.ofNat 64 (j + k)) (n - (j + k)) = bytesAt m₀ (D + BitVec.ofNat 64 (j + k)) (n - (j + k)) := by
  rw [bytesAt_frame hf hd (by omega)]
  rw [show n - j = k + (n - (j + k)) by omega] at h
  have := (bytesAt_split_eq h).2
  rwa [add_ofNat_assoc] at this

omit L in
/-- The first bytes, from the rest. -/
theorem rest_head {D : Addr} {n j k : Nat} (hk : j + k ≤ n) {m₀ m : Mem}
    (h : bytesAt m (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) :
    bytesAt m (D + BitVec.ofNat 64 j) k = bytesAt m₀ (D + BitVec.ofNat 64 j) k := by
  rw [show n - j = k + (n - j - k) by omega] at h
  exact (bytesAt_split_eq h).1

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {x₀ : List Byte} {P₀ : Nat} {enc : Bool}
  {D : Addr} {n : Nat} {m₀ : Mem}

theorem SInv.rounds {j : Nat} {s : State} (K : SCtx M Ctx St W SP R H D n m₀)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) : RoundsAt s.mem W R :=
  rounds_frame h.frame (fun r hr => w_stFrame K.lay h.data.ok.w K.t_w (by decide) (by decide) r hr) K.rounds

theorem SInv.hH {j : Nat} {s : State} (K : SCtx M Ctx St W SP R H D n m₀)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H := by
  rw [blockAt_frame h.frame fun r hr => (ctx_stFrame K.lay h.data.ctx K.t_c r hr).sub_left (Lay.ctxSub (by decide)),
    K.hH]

theorem SInv.ciph {j : Nat} {s : State} (K : SCtx M Ctx St W SP R H D n m₀)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R :=
  ciph_frame h.frame (ctx_stFrame K.lay h.data.ctx K.t_c) K.rounds.2

/-- The key context, for the data left from byte `j`. -/
theorem SInv.ext {j : Nat} {s : State} (K : SCtx M Ctx St W SP R H D n m₀)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) :
    CtxExt M Ctx St W SP (D + BitVec.ofNat 64 j) (n - j) s := by
  have hlt := h.data.ok.lt
  have hj := h.le
  refine ⟨K.xw, K.xs, K.xw', K.xd.sub_right (Offset.sub_base D (by omega)), K.xt, h.cov,
    M.frame h.frame (fun r hr => ?_) K.xw K.xok⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.xs.sub_right (Lay.stSub (by decide))
  · exact K.xd
  · exact K.xw'.sub_right (Lay.wSub (by decide))
  · exact K.xw'.sub_right (Lay.wSub (by decide))
  · exact K.xw'.sub_right (Lay.wSub (by decide))
  · exact K.xt.symm

/-- After code changing registers other than those `Env` holds. -/
theorem SInv.regs {j : Nat} {s s' : State} (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s' :=
  ⟨h.env.keep hg hrd hwr, h.data.of_eq hrd hwr, h.le, hm ▸ h.frame, hm ▸ h.rest, fun hy => hm ▸ h.abs hy,
    fun hy => hm ▸ h.ctr hy, fun hy => hm ▸ h.out hy, by rw [hrd, hwr]; exact h.cov⟩

/-- After code writing only the slots of `W` from `192`. -/
theorem SInv.slots {j : Nat} {s s' : State} (K : SCtx M Ctx St W SP R H D n m₀)
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    {d k : Nat} (h₁ : 192 ≤ d) (h₂ : d + k ≤ 224) (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] s.mem s'.mem) :
    SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s' := by
  have L := K.lay
  have hD := h.data.ok
  have one : ∀ {r : Region}, r.Disjoint ⟨W, 2560⟩ → ∀ r' ∈ [(⟨W + BitVec.ofNat 64 d, k⟩ : Region)], r.Disjoint r' :=
    fun hr r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr.sub_right (Lay.wSub (by omega))
  have hlt := hD.lt
  have hj := h.le
  refine ⟨h.env.keep hg hrd hwr, h.data.of_eq hrd hwr, h.le, h.frame.trans (slots_st h₁ h₂ hf), ?_,
    fun hy => abs_frame hf (fun r hr => ?_) (h.abs hy), fun hy => ctr_frame hf (fun r hr => ?_) (h.ctr hy),
    fun hy => by rw [bytesAt_frame hf (one (hD.w.sub_left (Region.sub_prefix h.le))) (by omega)]; exact h.out hy,
    by rw [hrd, hwr]; exact h.cov⟩
  · rw [bytesAt_frame hf (one (hD.w.sub_left (Offset.sub_base D (by omega)))) (by omega)]; exact h.rest
  · simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by decide) (.inr ⟨by omega, by omega⟩)
  · simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by decide) (.inr ⟨by omega, by omega⟩)

end

/-! ## The blocks of code between the calls -/

section
variable {Ctx St W SP : Addr}

/-- The data kept, its length and the text so far modulo 16. -/
theorem load_ok {s : State} (he : Env Ctx St W SP s) {Dj : Addr} {k : Nat} {T : BitVec 64}
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = Dj) (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = T) :
    ∃ s', runBlock isa streamLoad s = some s' ∧ s'.gpr .r12 = Dj ∧ s'.gpr .rbp = BitVec.ofNat 64 k ∧
      s'.gpr .rbx = BitVec.ofNat 64 (T.toNat % 16) ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold streamLoad
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have hand := and15 T
  rw [imm_eq (by decide)] at hand
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hdat]
  · simp [gpr_setReg, hlen]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, htl, hand]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

theorem load_env {s s' : State}
    (hg : ∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s'.gpr r = s.gpr r) :
    ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)

/-- Whether there are fewer than 256 bytes. -/
theorem small_ok (s : State) {n : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ s', runBlock isa streamSmall s = some s' ∧ s'.cf = some (decide (n < 256)) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold streamSmall
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_setReg, ite_true, hbp, setWidth_imm, toNat_ofNat_of_lt hn,
      toNat_ofNat_of_lt (show 256 < 2 ^ 64 by decide), show (256 : Nat) % 2 ^ 32 = 256 from rfl]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals rfl

/-- The length of the head. -/
def headLen (P n : Nat) : Nat := if P % 16 = 0 then 0 else min (16 - P % 16) n

theorem headLen_le (P n : Nat) : headLen P n ≤ n := by unfold headLen; split <;> omega

/-- After the head, the text so far is a whole number of blocks, unless
the data is used up. -/
theorem headLen_whole (P n : Nat) : n - headLen P n = 0 ∨ (P + headLen P n) % 16 = 0 := by
  unfold headLen; split <;> omega

/-- `streamHead`: the length of the head, kept and in `rbp`, and the whole
length at `auxO`. -/
theorem sHead_ok {s : State} (he : Env Ctx St W SP s) {P n : Nat} (hn : n < 2 ^ 64)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 (P % 16)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n) :
    WP isa streamHead s fun s' => s'.gpr .rbp = BitVec.ofNat 64 (headLen P n) ∧
      (∀ r, r ≠ .rbp → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (headLen P n) ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n ∧
      Frame [⟨W + BitVec.ofNat 64 208, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := Nat.mod_lt P (show 16 > 0 by decide)
  have w₁ := he.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have hz := and_self_beq (show P % 16 < 2 ^ 64 by omega)
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.store (at_ .r15 auxO) .rbp,
      .alu .test .rbx (.reg .rbx)] s = some s₁ ∧ s₁.zf = some (decide (P % 16 = 0)) ∧ s₁.gpr = s.gpr ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 n) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbx, hz]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg, gpr_arithFlags,
      he.r15, hbp]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hbx₁ : s₁.gpr .rbx = BitVec.ofNat 64 (P % 16) := by rw [hg₁, hbx]
  have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 n := by rw [hg₁, hbp]
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (headLen P n) ∧
      (∀ r, r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    (WP.ite (decide (P % 16 = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)) fun s₂ h₂ => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    apply WP.of_runBlock
    refine ⟨_, by xrun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, headLen, h0, imm_eq]
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_setReg, rd_setReg, wr_setReg]
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    refine WP.mono (minLen_ok s₁ hbx₁ hbp₁ (by omega) hn) fun s₂ ⟨hcx, hg, hm, hrd, hwr⟩ => ⟨?_, hg, hm, hrd, hwr⟩
    rw [hcx]; simp only [headLen, h0, ↓reduceIte]
  obtain ⟨hcx, hg₂, hm₂, hrd₂, hwr₂⟩ := h₂
  have h15 : s₂.gpr .r15 = W := by rw [hg₂ _ (by decide), hg₁, he.r15]
  have w₂' : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 208) 8 := by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact in_left w₂
  have w₂'' : InRegions s₂.wr (W + BitVec.ofNat 64 208) 8 := by rw [hwr₂, hwr₁]; exact w₂
  apply WP.of_runBlock
  have sep : Mem.Sep (W + BitVec.ofNat 64 216) (64 / 8) (W + BitVec.ofNat 64 208) (64 / 8) :=
    Offset.sep _ (.inr (by decide)) (by omega) (by omega)
  refine ⟨_, by xrun [h15, w₂'', hcx], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hcx]
  · intro r a b; simp [gpr_setReg, a, b, hg₂ r b, hg₁]
  · simp [mem_setReg, Mem.readW_writeW_self64]
  · simp only [mem_setReg, hm₂, hm₁]
    rw [Mem.readW_writeW_sep (sep_of_disj (Offset.disjoint _ (.inr (by decide)) (by omega)
      (by omega))) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_setReg, hm₂, hm₁]
    have c : ∀ d, 208 ≤ d → d + 8 ≤ 224 → (⟨W + BitVec.ofNat 64 208, 16⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  all_goals simp [rd_setReg, wr_setReg, hrd₂, hwr₂, hrd₁, hwr₁]

/-- `streamNext`: past the head of `k` bytes, of `n`. -/
theorem next_ok {s : State} (he : Env Ctx St W SP s) {D : Addr} {P k n : Nat} (hk : k ≤ n) (hn : n < 2 ^ 64)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P)
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    WP isa (.block streamNext) s fun s' => (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 k ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P + k) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - k) ∧
      Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold streamNext
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₄ := he.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a ≤ 2560 → d ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have eadd : BitVec.ofNat 64 P + BitVec.ofNat 64 k = BitVec.ofNat 64 (P + k) := (BitVec.ofNat_add _ _).symm
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := ofNat_sub hk hn
  have e₁ : (s.mem.writeW (W + BitVec.ofNat 64 200) (D + BitVec.ofNat 64 k)).readW (W + BitVec.ofNat 64 192) 64 =
      BitVec.ofNat 64 P := by rw [Mem.readW_writeW_sep (sep 192 200 (by decide) (by decide) (by decide)) (by decide), htl]
  have e₂ : ((s.mem.writeW (W + BitVec.ofNat 64 200) (D + BitVec.ofNat 64 k)).writeW (W + BitVec.ofNat 64 192)
      (BitVec.ofNat 64 (P + k))).readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n := by
    rw [Mem.readW_writeW_sep (sep 216 192 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 216 200 (by decide) (by decide) (by decide)) (by decide), haux]
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, q₄, w₁, w₂, w₃, hlen, hdat, eadd, e₁, e₂, esub], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 200 208 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 200 192 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 192 208 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_self64]
  · have c : ∀ d, 192 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 192, 24⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_arithFlags, mem_setReg]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

/-! ## Regions the pieces write -/

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem slot_crFrame {s : State} {Dj : Addr} {k d : Nat} (hd : DataOk St W SP s Dj k) (h₁ : 176 ≤ d)
    (h₂ : d + 8 ≤ 512) : ∀ r ∈ crFrame St W SP Dj k, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.w.sub_right (Lay.wSub (by omega))).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem slot_absFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ absFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem abs_crFrame {s : State} {Dj : Addr} {k : Nat} (hd : DataOk St W SP s Dj k) :
    ∀ r ∈ crFrame St W SP Dj k, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by decide)).symm

theorem ctr_absFrame : ∀ r ∈ absFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by decide)).symm

theorem ctxAll_absFrame : ∀ r ∈ absFrame St W SP 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
/-- Part of the data, apart from the part `crypt` writes. -/
theorem dsub_crFrame {s : State} {D : Addr} {n j k e l : Nat} (hd : DataOk St W SP s D n) (hk : j + k ≤ n)
    (hel : e + l ≤ n) (hs : e + l ≤ j ∨ j + k ≤ e) :
    ∀ r ∈ crFrame St W SP (D + BitVec.ofNat 64 j) k, (⟨D + BitVec.ofNat 64 e, l⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 e, l⟩ ⟨D, n⟩ := Offset.sub_base D hel
  have hlt := hd.lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint D hs (by omega) (by omega)
  · exact (hd.st.sub_left hsub).sub_right (Lay.stSub (by decide))
  · exact (hd.w.sub_left hsub).sub_right (Lay.wSub (by decide))
  · exact (hd.stk.sub_right hsub).symm

omit L in
theorem dsub_absFrame {s : State} {D : Addr} {n e l : Nat} (hd : DataOk St W SP s D n) (hel : e + l ≤ n) :
    ∀ r ∈ absFrame St W SP 16, (⟨D + BitVec.ofNat 64 e, l⟩ : Region).Disjoint r := fun r hr =>
  (data_absFrame (yo := 16) (.inr rfl) hd r hr).sub_left (Offset.sub_base D hel)

end

theorem dprefix (D : Addr) (j : Nat) : (⟨D, j⟩ : Region) = ⟨D + BitVec.ofNat 64 0, j⟩ := by rw [BitVec.add_zero]

/-! ## A part of the data: `crypt` and `absorb` -/

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {x₀ : List Byte} {P₀ : Nat}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `k` more bytes, from byte `j`: encrypted and absorbed, or absorbed and
decrypted. -/
theorem part_ok (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {j k : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s)
    (hx : x₀.length % 16 = P₀ % 16) (hk : j + k ≤ n)
    (h12 : s.gpr .r12 = D + BitVec.ofNat 64 j) (hbp : s.gpr .rbp = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 ((P₀ + j) % 16))
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 k)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j)) :
    WP isa (if enc then .seq (crypt v.callees) (.seq (.block streamLoad) (absorb v.callees 16))
      else .seq (absorb v.callees 16) (.seq (.block streamLoad) (crypt v.callees))) s fun s' =>
      SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ (j + k) s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  have L := K.lay
  have hD := h.data
  have hlt := hD.ok.lt
  have hj := h.le
  have hdj : DataW Ctx St W SP s (D + BitVec.ofNat 64 j) k := (hD.drop hj).take (by omega)
  have hR := h.rounds K
  have hH := h.hH K
  have hc := h.ciph K
  have hin : bytesAt s.mem (D + BitVec.ofNat 64 j) k = bytesAt m₀ (D + BitVec.ofNat 64 j) k := rest_head hk h.rest
  have hxl : (x₀ ++ ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = (P₀ + j) % 16 := by
    rw [List.length_append, length_ctext, length_bytesAt]; omega
  have hpre : ∀ r ∈ crFrame St W SP (D + BitVec.ofNat 64 j) k, (⟨D, j⟩ : Region).Disjoint r := by
    rw [dprefix]; exact dsub_crFrame hD.ok hk (by omega) (.inl (by omega))
  have hpreA : ∀ r ∈ absFrame St W SP 16, (⟨D, j⟩ : Region).Disjoint r := by
    rw [dprefix]; exact dsub_absFrame hD.ok (by omega)
  have hrestC := dsub_crFrame hD.ok hk (e := j + k) (l := n - (j + k)) (by omega) (.inr (by omega))
  have hrestA := dsub_absFrame hD.ok (e := j + k) (l := n - (j + k)) (by omega)
  cases enc
  · -- Decrypting: the ciphertext absorbed, then decrypted.
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext false (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s := ⟨h.env, h12, hbp, by rw [hbx, hxl], hdj.ok, hH⟩
    refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) hai)) fun s₂ ⟨ao, rd₂, wr₂⟩ => ?_)
    have sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok ao.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ := ao.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    have hc₂ : ciphOf s₂.mem Ctx R = ciphOf m₀ Ctx R := by rw [ciph_frame ao.frame (ctxAll_absFrame L) hR.2, hc]
    have hR₃ : RoundsAt s₃.mem W R := hm₃ ▸ rounds_frame ao.frame (slot_absFrame L (by decide) (by decide)) hR
    have hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    refine WP.mono (WP.with_rdwr (crypt_ok v L (icb := icb) ⟨he₃, h12₃, hbp₃, hbx₃, hdj₃, hR₃⟩))
      fun s₄ ⟨co, rd₄, wr₄⟩ => ⟨⟨co.env, hD.of_eq (by rw [rd₄, hrd₃, rd₂]) (by rw [wr₄, hwr₃, wr₂]), hk,
        h.frame.trans ((absFrame_st ao.frame).trans (hm₃ ▸ crFrame_st hk co.frame)), ?_, fun hy => ?_, fun hy => ?_,
        fun hy => ?_, by rw [rd₄, hrd₃, rd₂, wr₄, hwr₃, wr₂]; exact h.cov⟩, fun d h₁ h₂ => ?_⟩
    · rw [bytesAt_frame co.frame hrestC (by omega), hm₃, bytesAt_frame ao.frame hrestA (by omega)]
      exact rest_step hk hlt (Frame.refl (rs := []) _) (fun _ h => by cases h) h.rest
    · have A := abs_frame co.frame (abs_crFrame L hdj₃.ok) (hm₃ ▸ ao.abs (h.abs hy))
      rw [hin] at A
      simp only [ctext, Bool.false_eq_true, ↓reduceIte] at A ⊢
      rw [bytesAt_add, ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hm₃, hc₂] at C
      rw [← Nat.add_assoc]
      exact C (ctr_frame ao.frame (ctr_absFrame L) (h.ctr hy))
    · have C := co.out
      rw [hm₃, hc₂] at C
      have o := C (ctr_frame ao.frame (ctr_absFrame L) (h.ctr hy))
      rw [bytesAt_frame ao.frame (dsub_absFrame hD.ok (by omega)) (by omega), hin] at o
      refine done_append ?_ o
      rw [bytesAt_frame co.frame hpre (by omega), hm₃, bytesAt_frame ao.frame hpreA (by omega)]
      exact h.out hy
    · rw [co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (slot_crFrame L hdj₃.ok h₁ (by omega)) (by decide), hm₃, sl₂ d h₁ h₂]
  · -- Encrypting: the plaintext encrypted, then the ciphertext absorbed.
    simp only [↓reduceIte]
    refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok v L (icb := icb) ⟨h.env, h12, hbp, hbx, hdj, hR⟩))
      fun s₂ ⟨co, rd₂, wr₂⟩ => ?_)
    have sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
      co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hdj.ok h₁ (by omega))
        (by decide)
    obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok co.env
      ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
      ((sl₂ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ := co.env.keep (load_env hg₃) hrd₃ hwr₃
    rw [toNat_mod16] at hbx₃
    have hdj₃ : DataW Ctx St W SP s₃ (D + BitVec.ofNat 64 j) k := hdj.of_eq (hrd₃.trans rd₂) (hwr₃.trans wr₂)
    have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₃, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdj r hr).sub_left (Lay.ctxSub (by decide))), hH]
    have hai : AbsIn Ctx St W SP 16 H (x₀ ++ ctext true (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j))
        (D + BitVec.ofNat 64 j) k s₃ := ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hxl], hdj₃.ok, hH₃⟩
    refine WP.mono (WP.with_rdwr (absorb_ok v L (yo := 16) (.inr rfl) hai))
      fun s₄ ⟨ao, rd₄, wr₄⟩ => ⟨⟨ao.env, hD.of_eq (by rw [rd₄, hrd₃, rd₂]) (by rw [wr₄, hwr₃, wr₂]), hk,
        h.frame.trans ((crFrame_st hk co.frame).trans (hm₃ ▸ absFrame_st ao.frame)), ?_, fun hy => ?_, fun hy => ?_,
        fun hy => ?_, by rw [rd₄, hrd₃, rd₂, wr₄, hwr₃, wr₂]; exact h.cov⟩, fun d h₁ h₂ => ?_⟩
    · rw [bytesAt_frame ao.frame hrestA (by omega), hm₃]
      exact rest_step hk hlt co.frame hrestC h.rest
    · have C := co.out
      rw [hc] at C
      have o := C (h.ctr hy)
      rw [hin] at o
      have A := ao.abs (hm₃ ▸ abs_frame co.frame (abs_crFrame L hdj.ok) (h.abs hy))
      rw [hm₃, o] at A
      rw [bytesAt_add, ctext_append, length_bytesAt, ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hc] at C
      rw [← Nat.add_assoc]
      exact ctr_frame ao.frame (ctr_absFrame L) (hm₃ ▸ C (h.ctr hy))
    · have C := co.out
      rw [hc] at C
      have o := C (h.ctr hy)
      rw [hin] at o
      refine done_append ?_ ?_
      · rw [bytesAt_frame ao.frame hpreA (by omega), hm₃, bytesAt_frame co.frame hpre (by omega)]
        exact h.out hy
      · rw [bytesAt_frame ao.frame (dsub_absFrame hD.ok (by omega)) (by omega), hm₃]
        exact o
    · rw [ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (slot_absFrame L h₁ (by omega)) (by decide), hm₃, sl₂ d h₁ h₂]

end

/-! ## The whole blocks: one call -/

section
variable {Ctx St W SP : Addr}

/-- The number of whole blocks left. -/
theorem sb1_ok {L : Nat} (hL : L < 2 ^ 64) {s : State} (he : Env Ctx St W SP s)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) s fun s₁ =>
      s₁.gpr .rax = BitVec.ofNat 64 (L / 16) ∧ s₁.zf = some (decide (L / 16 = 0)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have h4 := shr4 L hL
  have hz := and_self_beq (show L / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, hlen, h4], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- After the call: the data kept, its length and the text so far past the
whole blocks. -/
theorem sb3_ok {Dj : Addr} {L T : Nat} (hL : L < 2 ^ 64) {s : State} (he : Env Ctx St W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = Dj)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 L)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 T) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
      .store (at_ .r15 lenO) .rcx, .alu .sub .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 dataO)),
      .alu .add .rcx (.reg .rax), .store (at_ .r15 dataO) .rcx, .mov .rcx (.mem (at_ .r15 tlenO)),
      .alu .add .rcx (.reg .rax), .store (at_ .r15 tlenO) .rcx]) s fun s₅ =>
      (∀ r, r ≠ .rax → r ≠ .rcx → s₅.gpr r = s.gpr r) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 200) 64 = Dj + BitVec.ofNat 64 (16 * (L / 16)) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (L % 16) ∧
      s₅.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (T + 16 * (L / 16)) ∧
      Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem s₅.mem ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr := by
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 200 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 208 + 8 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 192 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 L)
  rw [toNat_ofNat_of_lt hL, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 L - BitVec.ofNat 64 (L % 16) = BitVec.ofNat 64 (16 * (L / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hL]; congr 1; omega
  have eadd : BitVec.ofNat 64 T + BitVec.ofNat 64 (16 * (L / 16)) = BitVec.ofNat 64 (T + 16 * (L / 16)) :=
    (BitVec.ofNat_add _ _).symm
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a ≤ 2560 → d ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have e₁ : (s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (L % 16))).readW (W + BitVec.ofNat 64 200) 64 = Dj := by
    rw [Mem.readW_writeW_sep (sep 200 208 (by decide) (by decide) (by decide)) (by decide), hdat]
  have e₂ : ((s.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 (L % 16))).writeW (W + BitVec.ofNat 64 200)
      (Dj + BitVec.ofNat 64 (16 * (L / 16)))).readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 T := by
    rw [Mem.readW_writeW_sep (sep 192 200 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 192 208 (by decide) (by decide) (by decide)) (by decide), htl]
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, w₁, w₂, w₃, hlen, e15, esub, e₁, e₂, eadd], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 200 192 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_sep (sep 208 192 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep 208 200 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · simp only [mem_arithFlags, mem_setReg]
    rw [Mem.readW_writeW_self64]
  · have c : ∀ d, 192 ≤ d → d + 8 ≤ 216 → (⟨W + BitVec.ofNat 64 192, 24⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_arithFlags, mem_setReg]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

section
variable {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- The call of `vg_aes_gcm_encrypt_blocks` (`enc`) or `_decrypt_blocks`:
GHASH absorbs the ciphertext, which it writes or reads. -/
theorem callBlocks_ok (enc : Bool) {R : Nat} {D : Addr} {n q : Nat} {s : State} (h : ObIn M Ctx St W SP R D n q s) :
    WP isa (.frame (.push [.rax]) (.call (if enc then B.enc else B.dec).name
      (if enc then B.enc else B.dec).code) (.pop .rax 1)) s fun s₄ =>
      (∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r) ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame (obFrame St W SP D q) s.mem s₄.mem ∧
      blocksAt s₄.mem D q = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (St + BitVec.ofNat 64 48))
        (blocksAt s.mem D q) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 48) =
        Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem (St + BitVec.ofNat 64 48)) ∧
      blockAt s₄.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
        (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt (if enc then s₄.mem else s.mem) D q) := by
  cases enc
  · exact obFrameD_ok L B h
  · exact obFrameE_ok L B h

/-- The slots of `W` are outside what the call writes. -/
theorem slot_obFrame {Dj : Addr} {k q : Nat} (hD : (⟨Dj, k⟩ : Region).Disjoint ⟨W, 2560⟩) (hq : q * 16 ≤ k)
    (t_w : (below SP 24).Disjoint ⟨W, 2560⟩) {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 240) :
    ∀ r ∈ obFrame St W SP Dj q, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by omega))).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (t_w.sub_right (Lay.wSub (by omega))).symm

omit L in
/-- Part of the data, apart from the whole blocks the call writes. -/
theorem dsub_obFrame {s : State} {D : Addr} {n j q e l : Nat} (hd : DataOk St W SP s D n)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (hk : j + q * 16 ≤ n) (hel : e + l ≤ n) (hs : e + l ≤ j ∨ j + q * 16 ≤ e) :
    ∀ r ∈ obFrame St W SP (D + BitVec.ofNat 64 j) q, (⟨D + BitVec.ofNat 64 e, l⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 e, l⟩ ⟨D, n⟩ := Offset.sub_base D hel
  have hlt := hd.lt
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hd.st.sub_left hsub).sub_right (Lay.stSub (by decide))
  · exact (hd.st.sub_left hsub).sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint D hs (by omega) (by omega)
  · exact (hd.w.sub_left hsub).sub_right (Lay.wSub (by decide))
  · exact (t_d.sub_right hsub).symm

theorem buf_obFrame {Dj : Addr} {k q : Nat} (hD : (⟨Dj, k⟩ : Region).Disjoint ⟨St, 80⟩) (hq : q * 16 ≤ k)
    (t_s : (below SP 24).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ obFrame St W SP Dj q, (⟨St + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (t_s.sub_right (Lay.stSub (by decide))).symm

theorem ks_obFrame {Dj : Addr} {k q : Nat} (hD : (⟨Dj, k⟩ : Region).Disjoint ⟨St, 80⟩) (hq : q * 16 ≤ k)
    (t_s : (below SP 24).Disjoint ⟨St, 80⟩) :
    ∀ r ∈ obFrame St W SP Dj q, (⟨St + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [obFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.st_st (.inr (by decide)) (by decide) (by decide)
  · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (t_s.sub_right (Lay.stSub (by decide))).symm

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {x₀ : List Byte} {P₀ : Nat}
  {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamBlocks`: the whole blocks of the data left, from byte `j`, in one
call, when the text so far is a whole number of blocks. -/
theorem blocks_ok (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {j : Nat} {s : State}
    (h : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s) (hx : x₀.length % 16 = P₀ % 16)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 j)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - j))
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + j))
    (hal : (n - j) / 16 ≠ 0 → (P₀ + j) % 16 = 0) :
    WP isa (streamBlocks (if enc then B.enc else B.dec)) s fun s' =>
      SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ (j + 16 * ((n - j) / 16)) s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 ((n - j) % 16) ∧
      s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (P₀ + (j + 16 * ((n - j) / 16))) := by
  have L := K.lay
  have hD := h.data
  have hlt := hD.ok.lt
  have hj := h.le
  have he := h.env
  generalize hq : (n - j) / 16 = q
  unfold streamBlocks
  refine WP.seq (WP.mono (sb1_ok (L := n - j) (by omega) he hlen) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at r₁ z₁
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have h₁ : SInv M Hyp Ctx St W SP R H icb x₀ P₀ enc D n m₀ j s₁ := h.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) m₁ rd₁ wr₁
  refine WP.ite (decide (q = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    subst hz
    refine WP.block_nil ⟨by simpa using h₁, by rw [m₁, hdat]; simp, by rw [m₁, hlen]; congr 1; omega,
      by rw [m₁, htl]; simp⟩
  · simp only [decide_eq_false_iff_not] at hz
    have h0 : (P₀ + j) % 16 = 0 := hal (by omega)
    have hqk : j + q * 16 ≤ n := by omega
    have hR₁ := h₁.rounds K
    refine WP.seq (WP.mono (ob2_ok (D := D + BitVec.ofNat 64 j) he₁ hR₁ (by rw [m₁]; exact hdat))
      fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    have m₂' : s₂.mem = s.mem := m₂.trans m₁
    have hdq : DataW Ctx St W SP s₂ (D + BitVec.ofNat 64 j) (n - j) := (hD.drop hj).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)
    have obi : ObIn M Ctx St W SP R (D + BitVec.ofNat 64 j) (n - j) q s₂ := ⟨he₂, hdq, by omega, K.t_c, K.t_w,
      K.t_d.sub_right (Offset.sub_base D (by omega)), K.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, K.rounds.2, K.t_s,
      (h.ext K).of_eq (rd₂.trans rd₁) (wr₂.trans wr₁) m₂'⟩
    refine WP.seq (WP.mono (callBlocks_ok B L enc obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₁, o₂, o₃⟩ => ?_)
    have he₄ : Env Ctx St W SP s₄ := he₂.of_saved cs₄ rd₄ wr₄
    have kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (slot_obFrame L hdq.ok.w (by omega) K.t_w h₁ h₂) (by decide), m₂']
    refine WP.mono (sb3_ok (L := n - j) (by omega) he₄ ((kp 200 (by decide) (by decide)).trans hdat)
      ((kp 208 (by decide) (by decide)).trans hlen) ((kp 192 (by decide) (by decide)).trans htl))
      fun s₅ ⟨g₅, d₅, l₅, t₅, f₅, rd₅, wr₅⟩ => ?_
    rw [hq] at d₅ t₅
    have he₅ : Env Ctx St W SP s₅ := he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)) rd₅ wr₅
    have one : ∀ {r : Region}, r.Disjoint ⟨W, 2560⟩ → ∀ r' ∈ [(⟨W + BitVec.ofNat 64 192, 24⟩ : Region)],
        r.Disjoint r' := fun hr r' h' => by
      simp only [List.mem_singleton] at h'; subst h'; exact hr.sub_right (Lay.wSub (by decide))
    -- What the call did, from `m₀`.
    rw [m₂'] at o₁ o₂ o₃
    have hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R := h.ciph K
    have hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H := h.hH K
    rw [hc] at o₁
    rw [hH] at o₃
    have hin : bytesAt s.mem (D + BitVec.ofNat 64 j) (16 * q) = bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * q) :=
      rest_head (by omega) h.rest
    have hkd := Offset.sub_base D (d := j) (n := 16 * q) (k := n) (by omega)
    refine ⟨⟨he₅, hD.of_eq (by rw [rd₅, rd₄, rd₂, rd₁]) (by rw [wr₅, wr₄, wr₂, wr₁]), by omega,
      h.frame.trans ((m₂' ▸ obFrame_st hqk fr₄).trans (slots_st (Nat.le_refl _) (by decide) f₅)), ?_, fun hy => ?_,
      fun hy => ?_, fun hy => ?_, by rw [rd₅, rd₄, rd₂, rd₁, wr₅, wr₄, wr₂, wr₁]; exact h.cov⟩, by rw [d₅, add_ofNat_assoc], l₅,
      by rw [t₅, Nat.add_assoc]⟩
    · rw [bytesAt_frame f₅ (one (hD.ok.w.sub_left (Offset.sub_base D (by omega)))) (by omega)]
      exact rest_step (k := 16 * q) (by omega) hlt fr₄
        (dsub_obFrame hD.ok K.t_d hqk (by omega) (.inr (by omega))) (by rw [m₂']; exact h.rest)
    · have hx0 : (x₀ ++ ctext enc (ciphOf m₀ Ctx R) icb P₀ (bytesAt m₀ D j)).length % 16 = 0 := by
        rw [List.length_append, length_ctext, length_bytesAt]; omega
      have cw := Proof.Gcm.ctr_whole (h.ctr hy) h0 o₁ o₂
      have hZ : bytesAt (if enc then s₄.mem else s.mem) (D + BitVec.ofNat 64 j) (16 * q) =
          ctext enc (ciphOf m₀ Ctx R) icb (P₀ + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * q)) := by
        cases enc
        · simp only [Bool.false_eq_true, ↓reduceIte, ctext]; exact hin
        · simp only [↓reduceIte, ctext]; rw [cw.1, hin]
      have A₄ := Proof.Gcm.absorb_whole (m' := s₄.mem)
        (d := bytesAt (if enc then s₄.mem else s.mem) (D + BitVec.ofNat 64 j) (16 * q)) (h.abs hy) hx0
        (by rw [length_bytesAt]; omega) (by rw [o₃, Proof.Gcm.blocksAt_eq])
      have A₅ := abs_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)) A₄
      rw [hZ] at A₅
      rw [bytesAt_add, ctext_append, length_bytesAt, ← List.append_assoc]
      exact A₅
    · have cw := Proof.Gcm.ctr_whole (h.ctr hy) h0 o₁ o₂
      rw [← Nat.add_assoc]
      exact ctr_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)) cw.2
    · have cw := Proof.Gcm.ctr_whole (h.ctr hy) h0 o₁ o₂
      refine done_append ?_ ?_
      · rw [bytesAt_frame f₅ (one (hD.ok.w.sub_left (Region.sub_prefix hj))) (by omega),
          bytesAt_frame fr₄ (by rw [dprefix]; exact dsub_obFrame hD.ok K.t_d hqk (by omega) (.inl (by omega)))
            (by omega), m₂']
        exact h.out hy
      · rw [bytesAt_frame f₅ (one (hD.ok.w.sub_left hkd)) (by omega), cw.1, hin]

end

/-! ## The start, and all of `streamText` -/

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem}

/-- The additional data padded, if there is no text yet: then `SInv` holds,
with nothing done. -/
theorem start_ok (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State} (he : Env Ctx St W SP s)
    (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n) (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s fun s' =>
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ 0 s' ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
  have L := K.lay
  have hlt := hd.ok.lt
  have r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (c₀.length = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  have hm₂' : s₂.mem = m₀ := hm₂.trans hm
  have hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H := K.hH
  have dD : ∀ r ∈ tFrame St W SP 16, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hd.ok.st.sub_right (Lay.stSub (by decide))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
    · exact hd.ok.stk.symm
  have cT : ∀ r ∈ tFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.st_st (.inr (by decide)) (by decide) (by decide)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by decide)).symm
  have sT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  -- From a state with the padded additional data absorbed.
  have fin : ∀ s₄ : State, Env Ctx St W SP s₄ → s₄.rd = s.rd → s₄.wr = s.wr → Frame (tFrame St W SP 16) m₀ s₄.mem →
      (Hyp → Absorbed s₄.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length) ++ c₀)) →
      SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ 0 s₄ ∧
      ∀ d, 176 ≤ d → d + 8 ≤ 240 → s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun s₄ he₄ rd₄ wr₄ f₄ ha => ⟨⟨he₄, hd.of_eq rd₄ wr₄, Nat.zero_le _, tFrame_st f₄,
      by simpa using bytesAt_frame f₄ dD (by omega),
      fun hy => by simpa [bytesAt_zero, ctext_nil] using ha hy,
      fun hy => by simpa using ctr_frame f₄ cT (hyC hy), fun _ => rfl, by rw [rd₄, wr₄]; exact hcov⟩,
      fun d h₁ h₂ => by
        rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (sT d h₁ (by omega)) (by decide), hm]⟩
  refine WP.ite (decide (c₀.length = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => ?_)
  · have hc : c₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
    subst hc
    have r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
    obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (a.length % 16) ∧
        (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
      have hand := and15 (BitVec.ofNat 64 a.length)
      rw [imm_eq (by decide), toNat_mod16] at hand
      refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
      · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    unfold firstFlush
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    have hm₃' : s₃.mem = m₀ := hm₃.trans hm₂'
    refine WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (H := H) (x := a) ⟨he₃, by rw [hm₃']; exact hH⟩
      hbx₃)) fun s₄ ⟨fo, rd₄, wr₄⟩ => fin s₄ fo.env (by rw [rd₄, hrd₃, hrd₂]) (by rw [wr₄, hwr₃, hwr₂])
        (hm₃' ▸ fo.frame) fun hy => ?_
    rw [List.append_nil]
    exact fo.abs (by rw [hm₃']; exact hyA hy)
  · have hc : c₀ ≠ [] := fun e => by subst e; simp_all
    refine WP.block_nil (fin s₂ he₂ hrd₂ hwr₂ (by rw [hm₂']; exact Frame.refl _ _) fun hy => ?_)
    rw [hm₂', ← Proof.Gcm.ghashInput_of_ne hc]
    exact hyA hy

end

section
variable (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} {Hyp : Prop} {Ctx St W SP : Addr} {R : Nat} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem}

/-- `streamText enc`: the `n` bytes at `D` encrypted (`enc`) or decrypted,
and their ciphertext absorbed, after additional data `a` and text `c₀`. -/
theorem streamText_ok (B : BlkFn M) (K : SCtx M Ctx St W SP R H D n m₀) (enc : Bool) {s : State}
    (he : Env Ctx St W SP s) (hm : s.mem = m₀) (hd : DataW Ctx St W SP s D n)
    (hcov : Covers [⟨Ctx, M.len⟩] (s.rd ++ s.wr)) (hbp : s.gpr .rbp = BitVec.ofNat 64 n)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb c₀.length) :
    WP isa (streamText (v.withBlk B) enc) s fun s' => Env Ctx St W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) := by
  suffices WP isa (streamText (v.withBlk B) enc) s fun s' => Env Ctx St W SP s' ∧ Frame (stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) from
    WP.mono (WP.with_rdwr this) fun _ ⟨⟨a, b, c⟩, d, e⟩ => ⟨a, d, e, b, c⟩
  have hlt := hd.ok.lt
  have hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega
  simp only [streamText]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₁, by rw [hm₁, hm]; exact Frame.refl _ _, fun hy => ⟨?_, ?_, rfl⟩⟩
    · rw [bytesAt_zero, ctext_nil, List.append_nil, hm₁, hm]; exact hyA hy
    · rw [hm₁, hm]; exact hyC hy
  have h0 : n ≠ 0 := by simpa using hf
  have sl₁ : ∀ d, s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d => by
    rw [hm₁]
  refine WP.assoc (WP.seq (WP.mono (start_ok v K enc he₁ (hm₁.trans hm) (hd.of_eq hrd₁ hwr₁) (by rw [hrd₁, hwr₁]; exact hcov) (c₀ := c₀) hP
    (by rw [sl₁]; exact hal) (by rw [sl₁]; exact htl) hyA hyC) fun s₂ ⟨I₂, sl₂⟩ => ?_))
  -- The head.
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok I₂.env
    ((sl₂ 200 (by decide) (by decide)).trans ((sl₁ 200).trans hdat))
    ((sl₂ 208 (by decide) (by decide)).trans ((sl₁ 208).trans hlen))
    ((sl₂ 192 (by decide) (by decide)).trans ((sl₁ 192).trans htl))
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  have I₃ := I₂.regs (load_env hg₃) hm₃ hrd₃ hwr₃
  have sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃, sl₂ d h₁ h₂, sl₁]
  -- The end, from `SInv` over all the data.
  have fin : ∀ s', SInv M Hyp Ctx St W SP R H icb (a ++ zeros (padLen a.length) ++ c₀) c₀.length enc D n m₀ n s' →
      Env Ctx St W SP s' ∧ Frame (stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n)) := fun s' I => by
    refine ⟨I.env, I.frame, fun hy => ⟨?_, I.ctr hy, I.out hy⟩⟩
    have hne : c₀ ++ ctext enc (ciphOf m₀ Ctx R) icb c₀.length (bytesAt m₀ D n) ≠ [] := fun e => h0 (by
      have := congrArg List.length e
      rw [List.length_append, length_ctext, length_bytesAt, List.length_nil] at this
      omega)
    rw [Proof.Gcm.ghashInput_of_ne hne, ← List.append_assoc]
    exact I.abs hy
  -- Fewer than 256 bytes: all of them at once.
  obtain ⟨s₃', run₃', hcf, hg', hm', hrd', hwr'⟩ := small_ok s₃ hbp₃ hlt
  refine WP.seq (WP.of_runBlock ⟨s₃', run₃', ?_⟩)
  have I₃' := I₃.regs (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg' _ (by decide)) hm' hrd' hwr'
  have h12₃' : s₃'.gpr .r12 = D := by rw [hg' .r12 (by decide)]; exact h12₃
  have hbp₃' : s₃'.gpr .rbp = BitVec.ofNat 64 n := by rw [hg' .rbp (by decide)]; exact hbp₃
  have hbx₃' : s₃'.gpr .rbx = BitVec.ofNat 64 (c₀.length % 16) := by rw [hg' .rbx (by decide)]; exact hbx₃
  have sl₃' : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s₃'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm']; exact sl₃ d h₁ h₂
  refine WP.ite (decide (n < 256)) (eval_b hcf) (fun _ => ?_) (fun _ => ?_)
  · refine WP.mono (part_ok v K enc I₃' hx (j := 0) (k := n) (by omega) (by simp [h12₃']) hbp₃'
      (by rw [hbx₃', Nat.add_zero]) (by rw [sl₃' 200 (by decide) (by decide), hdat]; simp)
      (by rw [sl₃' 208 (by decide) (by decide), hlen]) (by rw [sl₃' 192 (by decide) (by decide), htl, Nat.add_zero]))
      fun s' ⟨I, _⟩ => fin s' (by rw [Nat.zero_add] at I; exact I)
  -- The head.
  refine WP.seq (WP.mono (sHead_ok I₃'.env hlt hbx₃' hbp₃') fun s₄ ⟨hbp₄, hg₄, hl₄, ha₄, f₄, hrd₄, hwr₄⟩ => ?_)
  generalize hk : headLen c₀.length n = k at hbp₄ hl₄
  have hkn : k ≤ n := hk ▸ headLen_le c₀.length n
  have hkw := headLen_whole c₀.length n
  rw [hk] at hkw
  have g₄ : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₄.gpr r = s₃'.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)
  have I₄ := I₃'.slots K g₄ hrd₄ hwr₄ (by decide) (by decide) f₄
  have sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 208 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [f₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K.lay.w_w (.inl (by omega)) (by omega) (by decide)) (by decide), sl₃' d h₁ (by omega)]
  refine WP.seq (WP.mono (part_ok v K enc I₄ hx (j := 0) (k := k) (by omega) (by simp [hg₄ .r12 (by decide) (by decide), h12₃'])
    hbp₄ (by rw [hg₄ .rbx (by decide) (by decide), hbx₃', Nat.add_zero]) (by rw [sl₄ 200 (by decide) (by decide), hdat]; simp) hl₄
    (by rw [sl₄ 192 (by decide) (by decide), htl, Nat.add_zero])) fun s₅ ⟨I₅, sl₅⟩ => ?_)
  -- Past the head.
  refine WP.seq (WP.mono (next_ok I₅.env (D := D) (P := c₀.length) hkn hlt (by rw [sl₅ 208 (by decide) (by decide), hl₄])
    (by rw [sl₅ 200 (by decide) (by decide), sl₄ 200 (by decide) (by decide), hdat])
    (by rw [sl₅ 192 (by decide) (by decide), sl₄ 192 (by decide) (by decide), htl])
    (by rw [sl₅ 216 (by decide) (by decide), ha₄])) fun s₆ ⟨g₆, d₆, t₆, l₆, f₆, hrd₆, hwr₆⟩ => ?_)
  have I₆ := I₅.slots K (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide)) hrd₆ hwr₆ (Nat.le_refl _) (by decide) f₆
  rw [Nat.zero_add] at I₆
  -- The whole blocks.
  refine WP.seq (WP.mono (blocks_ok B K enc I₆ hx d₆ l₆ t₆ (fun hq => hkw.resolve_left (by omega)))
    fun s₇ ⟨I₇, d₇, l₇, t₇⟩ => ?_)
  generalize hj₂ : k + 16 * ((n - k) / 16) = j₂ at I₇ d₇ t₇
  -- The rest.
  obtain ⟨s₈, run₈, h12₈, hbp₈, hbx₈, hg₈, hm₈, hrd₈, hwr₈⟩ := load_ok I₇.env d₇ l₇ t₇
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  rw [toNat_mod16] at hbx₈
  have I₈ := I₇.regs (load_env hg₈) hm₈ hrd₈ hwr₈
  refine WP.mono (part_ok v K enc I₈ hx (j := j₂) (k := (n - k) % 16) (by omega) h12₈ hbp₈ hbx₈
    (by rw [hm₈]; exact d₇) (by rw [hm₈]; exact l₇) (by rw [hm₈]; exact t₇)) fun s' ⟨I, _⟩ => ?_
  have hn : j₂ + (n - k) % 16 = n := by omega
  rw [hn] at I
  exact fin s' I

end

end VG.Proof.AesGcm.X86_64
