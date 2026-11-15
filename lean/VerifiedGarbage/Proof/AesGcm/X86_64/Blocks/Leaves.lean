module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fin
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Full
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on whole blocks, x86-64: what the encryption leaves in `scratch`

Untrusted: everything here is checked by Lean. What `vg_aes_gcm_encrypt_blocks`
leaves in its 2112 bytes of `scratch` at `S` (`Scr`): the arguments kept in
its first 48 bytes (`Kept`), and elsewhere, byte by byte, zero where `Z`
says, or what it held on entry. The entry writes only the arguments
(`Scr.entry`), `rest` only the slots of the data and of the number of blocks
(`rest_okF`), the calls of `vg_aes_ctr32` and `vg_ghash` that need no working
space nothing in `scratch` (`callsF`), and loops that write only the first `ℓ`
bytes of their working space, clearing those `zf` says
(`Gcm.X86_64.Stitch.PieceL`), clear those (`Scr.piece`). So for loops that clear what they write, what is left is
a function of the arguments (`encryptB_leaves`, `encryptR_leaves`).
-/

-- separate module: its one importer imports `Instances`, and with it every proof of AES-GCM on x86-64; these generic proofs need no re-checking when one of those changes

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Aes.X86_64 (Ctr32Impl Ctr32Free)

/-- Two postconditions of the same code from the same state: its run is
deterministic. -/
theorem wp_and {c : Prog isa} {s : State} {Q R : State → Prop} (h₁ : WP isa c s Q) (h₂ : WP isa c s R) :
    WP isa c s fun s' => Q s' ∧ R s' := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨_, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-- Byte `j` of a 64-bit little-endian read. -/
theorem byte_readW64 (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a hj]; rfl

/-- What `scratch` holds, in `m`: the arguments kept for what is left after
`k` blocks, and from byte 48 on, zero where `Z` says (of the offset), and
elsewhere what it held on entry. -/
structure Scr (s : State) (k : Nat) (Z : Nat → Bool) (m : Mem) : Prop where
  kept : Kept s k m
  rest : ∀ d, 48 ≤ d → d < 2112 → m (S s + BitVec.ofNat 64 d) = if Z d then 0 else s.mem (S s + BitVec.ofNat 64 d)

theorem contains_S (s : State) {d : Nat} (hd : d < 2112) : (sR s).Contains (S s + BitVec.ofNat 64 d) 1 :=
  Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

/-- After the entry: the arguments, nothing else written. -/
theorem Scr.entry {s : State} {m : Mem} (hk : Kept s 0 m) (hf : Frame [kR' s] s.mem m) :
    Scr s 0 (fun _ => false) m :=
  ⟨hk, fun d h48 h2 => by
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hf _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      change (S s + BitVec.ofNat 64 d - S s).toNat + 1 ≤ 48 at hc
      rw [Mem.sub_ofNat_toNat _ (by omega_using [h2])] at hc; omega_using [h48, hc]⟩

/-- Through writes apart from `scratch`. -/
theorem Scr.frame {s : State} {k : Nat} {Z : Nat → Bool} {m m' : Mem} (h : Scr s k Z m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sR s).Disjoint r) : Scr s k Z m' :=
  ⟨h.kept.frame hf fun r hr => (hd r hr).sub_left kR'_sub, fun d h1 h2 => by
    rw [hf _ fun r hr hc => hd r hr _ (contains_S s h2) hc]; exact h.rest d h1 h2⟩

/-- Through writes to the slots of the arguments. -/
theorem Scr.slots {s : State} {k k' : Nat} {Z : Nat → Bool} {m m' : Mem} (h : Scr s k Z m)
    (hf : Frame [kR' s] m m') (hk : Kept s k' m') : Scr s k' Z m' :=
  ⟨hk, fun d h1 h2 => by
    rw [hf _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      change (S s + BitVec.ofNat 64 d - S s).toNat + 1 ≤ 48 at hc
      rw [Mem.sub_ofNat_toNat _ (by omega_using [h2])] at hc; omega_using [h1, hc]]
    exact h.rest d h1 h2⟩

/-- Through interleaved loops whose working space is at `S + o`, which leave
`Gcm.X86_64.Stitch.PieceL ℓ zf`. -/
theorem Scr.piece {M : CtxMode} {s : State} (hp : BP M s) {Z : Nat → Bool} {s₃ s₄ : State} {o ℓ : Nat}
    {zf : Nat → Nat → Bool} (ho : 48 ≤ o) (hoℓ : o + ℓ ≤ 2112) (h : Scr s 0 Z s₃.mem)
    (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 o) (ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r)
    (hq : Gcm.X86_64.Stitch.nb s₃ ≤ n s) (hP : Gcm.X86_64.Stitch.PieceL ℓ zf s₃ s₄) :
    Scr s 0 (fun d => Z d || (decide (o ≤ d) && decide (d < o + ℓ) && zf (Gcm.X86_64.Stitch.nb s₃) (d - o)))
      s₄.mem := by
  obtain ⟨hf, hz⟩ := hP
  have ec : Gcm.X86_64.Stitch.cR s₃ = cR s := by
    simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.cp, ga _ (by simp [argRegs] : Reg.rdx ∈ argRegs)]
  have ey : Gcm.X86_64.Stitch.yR s₃ = yR s := by
    simp only [Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.yp, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs)]
  have ep : Gcm.X86_64.Stitch.pp s₃ = S s + BitVec.ofNat 64 o := h11
  have pd : Region.Sub (Gcm.X86_64.Stitch.dR s₃) (dR s) := by
    show Region.Sub ⟨s₃.gpr .r8, 16 * Gcm.X86_64.Stitch.nb s₃⟩ _
    rw [ga _ (by simp [argRegs])]; exact Region.sub_prefix (by omega_using [hq])
  rw [ec, ey, ep] at hf
  rw [ep] at hz
  have hws := hp.w_s
  refine ⟨h.kept.frame hf fun r hr => ?_, fun d h1 h2 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kR'_disj hp _ (by simp)
    · exact kR'_disj hp _ (by simp)
    · exact (kR'_disj hp (dR s) (by simp)).sub_right pd
    · exact Offset.base_disjoint _ ho (by omega_using [hoℓ])
  · by_cases hin : o ≤ d ∧ d < o + ℓ
    · have ex : S s + BitVec.ofNat 64 d = S s + BitVec.ofNat 64 o + BitVec.ofNat 64 (d - o) :=
        (Offset.add_add_eq _ (by omega_using [hin])).symm
      rw [ex, hz _ (by omega_using [hin]), ← ex, h.rest d h1 h2]
      simp only [decide_eq_true hin.1, decide_eq_true hin.2, Bool.true_and]
      cases Z d <;> cases zf (Gcm.X86_64.Stitch.nb s₃) (d - o) <;> simp only [Bool.or_true, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte, ite_self]
    · have hnot : (decide (o ≤ d) && decide (d < o + ℓ)) = false := by
        rw [Bool.eq_false_iff]; intro h'; simp only [Bool.and_eq_true, decide_eq_true_eq] at h'; exact hin h'
      rw [hf _ fun r hr hc => ?_, h.rest d h1 h2]
      · simp only [hnot, Bool.false_and, Bool.or_false]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hS := contains_S s h2
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.c_s.symm _ hS hc
        · exact hp.y_s.symm _ hS hc
        · exact hp.d_s.symm _ hS (pd _ hc)
        · change (S s + BitVec.ofNat 64 d - (S s + BitVec.ofNat 64 o)).toNat < ℓ at hc
          rw [Offset.lt_iff _ _ (by omega_using [hoℓ]), Mem.sub_ofNat_toNat _ (by omega_using [h2])] at hc
          exact hin hc

theorem Scr.congr {s : State} {k : Nat} {Z Z' : Nat → Bool} {m : Mem} (h : Scr s k Z m)
    (e : ∀ d, 48 ≤ d → d < 2112 → Z d = Z' d) : Scr s k Z' m :=
  ⟨h.kept, fun d h1 h2 => by rw [← e d h1 h2]; exact h.rest d h1 h2⟩

section
variable {M : CtxMode} {s : State} (hp : BP M s)
include hp

/-- `rest_ok`, and what `rest` writes: the slots of the arguments. -/
theorem rest_okF {q : Nat} (hq : q = n s - n s % 16) {ys : List Block} {st : State} (h : Mid s q 0 ys st) :
    WP isa (.block rest) st fun st' => Mid s q q ys st' ∧ Frame [kR' s] st.mem st'.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by
    rw [h.rsp, keep_a hp h.frame]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 32) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 40) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kd := h.kept.data
  have kn := h.kept.n
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kd kn
  have e15 := and15 (BitVec.ofNat 64 (n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (n s) - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2112 → d + 8 ≤ 2112 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega_using [ha]) (by omega_using [hd])
  have kp : ∀ d, d + 8 ≤ 32 → ∀ v w : BitVec 64,
      ((st.mem.writeW (S s + BitVec.ofNat 64 32) v).writeW (S s + BitVec.ofNat 64 40) w).readW
        (S s + BitVec.ofNat 64 d) 64 = st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ v w => by
    rw [Mem.readW_writeW_sep (sep d 40 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 32 (.inl (by omega_using [h₁])) (by omega_using [h₁]) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [rest, argData, argN]; xrun [a₀, hS, r₅, r₆, w₅, w₆, kn, e15, esub, times16_val, kd], ?_⟩
  have c : ∀ d, d + 8 ≤ 48 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ => Offset.contains_base _ h₁ (by omega_using [h₁])
  refine ⟨h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2, h3]) ?_ ?_ rfl rfl, ?_⟩
  rotate_left
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 32 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 40 (by decide))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := kp 0 (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h.kept.ctx
  · rw [kp 8 (by decide)]; exact h.kept.rounds
  · rw [kp 16 (by decide)]; exact h.kept.ctr
  · rw [kp 24 (by decide)]; exact h.kept.y
  · rw [Mem.readW_writeW_sep (sep 32 40 (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, BitVec.add_comm]
  · rw [Mem.readW_writeW_self64, hq]; congr 1; omega_using []

/-- The head of `tail`, which writes no memory. -/
theorem tailHeadL_ok {q : Nat} {ys : List Block} {st : State} (h : Mid s q q ys st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)])
      st fun st' => (Mid s q q ys st' ∧ st'.zf = some (decide (n s - q = 0))) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, keep_a hp h.frame]; rfl
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hz := and_self_beq (show n s - q < 2 ^ 64 by omega_using [hn])
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₀, hS, r₆, h.kept.n], ⟨?_, by simp only [zf_arithFlags, hz]⟩, ?_⟩
  · exact h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2]) h.kept (Frame.refl _ _) rfl rfl
  · simp [mem_arithFlags, mem_setReg]

omit hp in
theorem covers_sub {rs rs' ts : List Region} (h : Covers rs' ts) (hs : ∀ r ∈ rs, r ∈ rs') : Covers rs ts :=
  fun a m ⟨r, hr, hc⟩ => h a m ⟨r, hs r hr, hc⟩

omit hp in
theorem CtrCall.toF {st : State} {K C D S' : Addr} {R q : Nat} (h : CtrCall st K C D S' R q) :
    CtrCallF st K C D S' R q :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rounds, h.wrap, h.kc, h.kd, h.cd, h.stkK, h.stkC, h.stkD,
    covers_sub h.reads fun r hr => by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp,
    covers_sub h.writes fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp⟩

omit hp in
theorem GhCall.toF {st : State} {H Y' D S' : Addr} {q : Nat} (h : GhCall st H Y' D S' q) : GhCallF st H Y' D S' q :=
  ⟨h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.n_lt, h.hy, h.yd, h.stkH, h.stkY, h.stkD,
    covers_sub h.reads fun r hr => by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> simp,
    covers_sub h.writes fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp⟩

/-- What the calls of the encryption's `tail` write, with implementations of
`vg_aes_ctr32` and `vg_ghash` that need no working space: the counter, the
data left, `Y` and the return address. -/
theorem callsF (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {q : Nat} {ys : List Block} {st₁ : State} (M : Mid s q q ys st₁) (hlt : q < n s) :
    WP isa (.seq (ctrCall ⟨ctr.callee.name, ctr.callee.code⟩) (ghCall gh.fn)) st₁ fun st =>
      Frame [cR s, ⟨dq s q, 16 * (n s - q)⟩, below (SP s) 8, yR s] st₁.mem st.mem := by
  have hq := M.q_le
  refine WP.seq (WP.seq (WP.mono (ctrArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hc, R₂, _, m₂⟩ =>
    WP.mono (ctr_callF ctr cf (CtrCall.toF hc)) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have sub3 : ∀ r ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), below (SP s) 8],
      r ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8] := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp
  have R₃ : Ready s q st₃ := R₂.frame f₃ (fun r hr => (apart_kR' hp hq).ctr r (sub3 r hr))
    (fun r hr => (apart_a hp hq).ctr r (sub3 r hr)) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (ghArgs_ok hp R₃ hlt) fun st₄ ⟨hg, R₄, _, m₄⟩ =>
    WP.mono (gh_callF gh gf (GhCall.toF hg)) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  rw [m₄] at f₅
  rw [m₂] at f₃
  exact (f₃.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp).trans
    (f₅.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)

/-- `scratch` is apart from what the calls write. -/
theorem sR_calls {q : Nat} (hq : q ≤ n s) :
    ∀ r ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), below (SP s) 8, yR s], (sR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.c_s.symm
  · exact hp.d_s.symm.sub_right (dq_sub hq)
  · exact hp.t_s.symm
  · exact hp.y_s.symm

/-- `tail` with the calls of `callsF`: `scratch` as it was. -/
theorem tailL_ok (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {q : Nat} {ys : List Block} {Z : Nat → Bool} {st : State} (M : Mid s q q ys st) (hS : Scr s q Z st.mem) :
    WP isa (tail (ctrCall ⟨ctr.callee.name, ctr.callee.code⟩) (ghCall gh.fn)) st fun st' => Scr s q Z st'.mem := by
  refine WP.seq (WP.mono (tailHeadL_ok hp M) fun st₁ ⟨⟨M₁, hz⟩, hm⟩ => ?_)
  rw [← hm] at hS
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun _ => WP.block_nil hS) (fun e => ?_)
  have hlt : q < n s := by simp at e; omega_using [e]
  exact WP.mono (callsF hp ctr cf gh gf M₁ hlt) fun st' hf => hS.frame hf (sR_calls hp M₁.q_le)

/-- What the calls of the decryption's `tail` write, with implementations of
`vg_ghash` and `vg_aes_ctr32` that need no working space (`callsF`, the
other way round). -/
theorem callsD (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {q : Nat} {ys : List Block} {st₁ : State} (M : Mid s q q ys st₁) (hlt : q < n s) :
    WP isa (.seq (ghCall gh.fn) (ctrCall ⟨ctr.callee.name, ctr.callee.code⟩)) st₁ fun st =>
      Frame [cR s, ⟨dq s q, 16 * (n s - q)⟩, below (SP s) 8, yR s] st₁.mem st.mem := by
  have hq := M.q_le
  refine WP.seq (WP.seq (WP.mono (ghArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hg, R₂, _, m₂⟩ =>
    WP.mono (gh_callF gh gf (GhCall.toF hg)) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : Ready s q st₃ := R₂.frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (apart_kR' hp hq).y
      · exact (apart_kR' hp hq).t)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (apart_a hp hq).y
      · exact (apart_a hp hq).t) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (ctrArgs_ok hp R₃ hlt) fun st₄ ⟨hc, R₄, _, m₄⟩ =>
    WP.mono (ctr_callF ctr cf (CtrCall.toF hc)) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  rw [m₄] at f₅
  rw [m₂] at f₃
  exact (f₃.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans
    (f₅.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp)

/-- `tail` with the calls of `callsD`: `scratch` as it was. -/
theorem tailD_ok (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {q : Nat} {ys : List Block} {Z : Nat → Bool} {st : State} (M : Mid s q q ys st) (hS : Scr s q Z st.mem) :
    WP isa (tail (ghCall gh.fn) (ctrCall ⟨ctr.callee.name, ctr.callee.code⟩)) st fun st' => Scr s q Z st'.mem := by
  refine WP.seq (WP.mono (tailHeadL_ok hp M) fun st₁ ⟨⟨M₁, hz⟩, hm⟩ => ?_)
  rw [← hm] at hS
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun _ => WP.block_nil hS) (fun e => ?_)
  have hlt : q < n s := by simp at e; omega_using [e]
  exact WP.mono (callsD hp ctr cf gh gf M₁ hlt) fun st' hf => hS.frame hf (sR_calls hp M₁.q_le)

/-! ## Without interleaved loops -/

/-- `vg_aes_gcm_encrypt_blocks` without interleaved loops, with calls that
need no working space: `scratch` holds the arguments kept, and nothing else
written. -/
theorem encryptN_leaves (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code) :
    WP isa (encrypt ⟨ctr.callee.name, ctr.callee.code⟩ gh.fn none) s fun s' =>
      Scr s 0 (fun _ => false) s'.mem :=
  WP.seq (WP.mono (entry_ok hp) fun _ ⟨_, hg, hk, hf, hrd, hwr⟩ =>
    WP.seq (WP.block_nil (tailL_ok hp ctr cf gh gf (mid_entry hp hg hk hf hrd hwr) (Scr.entry hk hf))))

/-- `vg_aes_gcm_decrypt_blocks` without interleaved loops, with calls that
need no working space: `scratch` holds the arguments kept, and nothing else
written. -/
theorem decryptN_leaves (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code) :
    WP isa (decrypt ⟨ctr.callee.name, ctr.callee.code⟩ gh.fn none) s fun s' =>
      Scr s 0 (fun _ => false) s'.mem :=
  WP.seq (WP.mono (entry_ok hp) fun _ ⟨_, hg, hk, hf, hrd, hwr⟩ =>
    WP.seq (WP.block_nil (tailD_ok hp ctr cf gh gf (mid_entry hp hg hk hf hrd hwr) (Scr.entry hk hf))))

/-! ## Loops that take the first `16 ⌊n / 16⌋` blocks -/

/-- `stitchPart` of loops that also leave `Gcm.X86_64.Stitch.PieceL ℓ zf`, from the state after
the entry: `Mid`, as `stitchE_ok`, and `scratch`, the first `ℓ` bytes of
the working space cleared where `zf` says if the loops ran. -/
theorem stitchL_ok {aligned : Bool} {piece : Prog isa} {ℓ : Nat} {zf : Nat → Nat → Bool}
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ → Gcm.X86_64.Stitch.nb s₃ % 16 = 0 →
      WP isa piece s₃ fun s₄ => Gcm.X86_64.Stitch.EPost s₃ s₄ ∧ Gcm.X86_64.Stitch.PieceL ℓ zf s₃ s₄)
    (hoℓ : AlignedScratch.offset aligned (S s) + ℓ ≤ 2112)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem)
    (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece aligned) s₁ fun st =>
      Mid s (n s - n s % 16) 0 (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s - n s % 16))) st ∧
      Scr s 0 (fun d => decide (16 ≤ n s) && (decide (AlignedScratch.offset aligned (S s) ≤ d) &&
        decide (d < AlignedScratch.offset aligned (S s) + ℓ) &&
        zf (n s - n s % 16) (d - AlignedScratch.offset aligned (S s)))) st.mem := by
  have hS₀ := Scr.entry hk hf
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : n s - n s % 16 = 0 := by simp at h; omega_arith
    have hlt : ¬ 16 ≤ n s := by simp at h; omega_arith
    refine WP.block_nil ⟨?_, ?_⟩
    · rw [h0]
      exact mid_entry hp (fun r hr => by rw [g₂]; exact hg r hr) (by rw [m₂]; exact hk)
        (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr)
    · rw [m₂]; exact hS₀.congr fun d _ _ => by simp only [hlt, decide_false, Bool.false_and]
  · have h16 : 16 ≤ n s := by simp at h; omega_arith
    refine WP.seq (WP.mono (split_ok (s := s) (aligned := aligned) (by rw [g₂]; exact hg _ (by decide)))
      fun s₃ ⟨h9, h11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
    have ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₂,
        hg r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    have gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₂,
        hg r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    have g11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₃, g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    have rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    have wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans hwr)
    have hk₃ : Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    have hf₃ : Frame [kR' s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    have hnb : Gcm.X86_64.Stitch.nb s₃ = n s - n s % 16 := by
      simp only [Gcm.X86_64.Stitch.nb, h9, toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega_arith)]
    have hm : Gcm.X86_64.Stitch.nb s₃ % 16 = 0 := by rw [hnb]; omega_arith
    have hS₃ : Scr s 0 (fun _ => false) s₃.mem := by rw [m₃, m₂]; exact hS₀
    refine WP.mono (hpiece s₃ (spreM_of hp (by omega_arith) (by omega_arith) h9 ga g11 rd₃' wr₃' hf₃) hm)
      fun s₄ ⟨hP, hL⟩ => ⟨?_, ?_⟩
    · refine mid_of_post hp (by omega_arith) h9 ga gc g11 rd₃' wr₃' hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd
        hP.wr fun eH eY _ eD => ?_
      have hy := hP.y
      simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
        Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
        ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
        toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega_arith)] at hy
      rw [hy, eH, eY, eD]
    · have ho := AlignedScratch.offset_bounds aligned (S s)
      refine (Scr.piece hp (by omega_using [ho]) hoℓ hS₃ g11 ga (by rw [hnb]; omega_arith) hL).congr fun d _ _ => ?_
      simp only [hnb, h16, decide_true, Bool.true_and, Bool.false_or]

/-- `vg_aes_gcm_encrypt_blocks` with loops on the first `16 ⌊n / 16⌋` blocks
that clear the 256 bytes they write, and calls that need no working space:
what is left in `scratch`. -/
theorem encryptB_leaves (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {piece : Prog isa}
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ → Gcm.X86_64.Stitch.nb s₃ % 16 = 0 →
      WP isa piece s₃ fun s₄ => Gcm.X86_64.Stitch.EPost s₃ s₄ ∧ Gcm.X86_64.Stitch.PieceL 256 (fun _ _ => true) s₃ s₄) :
    WP isa (encrypt ⟨ctr.callee.name, ctr.callee.code⟩ gh.fn (some piece) false false) s fun s' =>
      Scr s (n s - n s % 16) (fun d => decide (16 ≤ n s) && decide (64 ≤ d) && decide (d < 320)) s'.mem := by
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ ⟨h11, hg, hk, hf, hrd, hwr⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (stitchL_ok hp (aligned := false) hpiece (by simp [AlignedScratch.offset])
    h11 hg hk hf hrd hwr) fun st ⟨M, hS⟩ => WP.mono (rest_okF hp rfl M) fun st' ⟨M', hf'⟩ => ?_))
  refine WP.mono (tailL_ok hp ctr cf gh gf M' ((hS.slots hf' M'.kept).congr fun d _ _ => ?_)) fun _ h => h
  simp only [AlignedScratch.offset, Bool.false_eq_true, ↓reduceIte, Bool.and_true, Bool.and_assoc]

/-! ## Loops that take all the blocks, from 2 on -/

/-- `Blocks.fullBody` with loops that take all the blocks from
`smallMin false = 2` on (`small`, and `pieceS` the same loops), which leave
`PieceL ℓ zf`, and calls that need no working space below that: `scratch`
after the entry's slots, the first `ℓ` bytes of the working space cleared
where `zf` says if the loops ran. -/
theorem fullBodyL_ok {aligned : Bool} {piece : Prog isa} {ℓ : Nat} {zf : Nat → Nat → Bool}
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ 1 →
      WP isa piece s₃ fun s₄ => Gcm.X86_64.Stitch.EPost s₃ s₄ ∧ Gcm.X86_64.Stitch.PieceL ℓ zf s₃ s₄)
    (hoℓ : AlignedScratch.offset aligned (S s) + ℓ ≤ 2112)
    (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem)
    (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (fullBody piece (ctrCall ⟨ctr.callee.name, ctr.callee.code⟩) (ghCall gh.fn) aligned true false
      (some piece) false) s₁ fun st =>
      Scr s 0 (fun d => decide (2 ≤ n s) && (decide (AlignedScratch.offset aligned (S s) ≤ d) &&
        decide (d < AlignedScratch.offset aligned (S s) + ℓ) &&
        zf (n s) (d - AlignedScratch.offset aligned (S s)))) st.mem := by
  have hS₀ := Scr.entry hk hf
  have ho := AlignedScratch.offset_bounds aligned (S s)
  -- The loops, from a state with `s₁`'s registers and memory.
  have pc : ∀ s₂ : State, 2 ≤ n s → s₂.gpr = s₁.gpr → s₂.mem = s₁.mem → s₂.rd = s₁.rd → s₂.wr = s₁.wr →
      WP isa (stitchPart piece aligned true) s₂ fun st =>
        Scr s 0 (fun d => decide (2 ≤ n s) && (decide (AlignedScratch.offset aligned (S s) ≤ d) &&
          decide (d < AlignedScratch.offset aligned (S s) + ℓ) &&
          zf (n s) (d - AlignedScratch.offset aligned (S s)))) st.mem := by
    intro s₂ h2 g₂ m₂ rd₂ wr₂
    refine WP.seq (WP.mono (scratch_ok (aligned := aligned) s₂) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
    have keepR : ∀ r, r ≠ .r11 → s₄.gpr r = s.gpr r := fun r c => by rw [g₄ r c, g₂, hg r c]
    have ga : ∀ r ∈ argRegs, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide)
    have g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₄, g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    have h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
      rw [keepR _ (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm
    have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₂, hrd]
    have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₂, hwr]
    have hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄, m₂]; exact hf
    have hn9 : Gcm.X86_64.Stitch.nb s₄ = n s := by
      show (s₄.gpr .r9).toNat = _
      rw [h9]; exact toNat_ofNat_of_lt (s.gpr .r9).isLt
    have hS₄ : Scr s 0 (fun _ => false) s₄.mem := by rw [m₄, m₂]; exact hS₀
    refine WP.mono (hpiece s₄ (spreM_of hp (lo := 1) (by omega_using [h2]) (Nat.le_refl _) h9 ga g11 rd₄' wr₄' hf₄))
      fun s₅ ⟨_, hL⟩ => ?_
    refine (Scr.piece hp (by omega_using [ho]) hoℓ hS₄ g11 ga (by rw [hn9]) hL).congr fun d _ _ => ?_
    simp only [hn9, decide_eq_true h2, Bool.true_and, Bool.false_or]
  -- The calls, from a state with `s₁`'s registers and memory.
  have cl : n s < 2 → ∀ s₂ : State, s₂.gpr = s₁.gpr → s₂.mem = s₁.mem → s₂.rd = s₁.rd → s₂.wr = s₁.wr →
      WP isa (.seq (.block rest) (tail (ctrCall ⟨ctr.callee.name, ctr.callee.code⟩) (ghCall gh.fn))) s₂ fun st =>
        Scr s 0 (fun d => decide (2 ≤ n s) && (decide (AlignedScratch.offset aligned (S s) ≤ d) &&
          decide (d < AlignedScratch.offset aligned (S s) + ℓ) &&
          zf (n s) (d - AlignedScratch.offset aligned (S s)))) st.mem := by
    intro hlt s₂ g₂ m₂ rd₂ wr₂
    have M := mid_entry hp (fun r hr => by rw [g₂]; exact hg r hr) (by rw [m₂]; exact hk) (by rw [m₂]; exact hf)
      (rd₂.trans hrd) (wr₂.trans hwr)
    have hS₂ : Scr s 0 (fun _ => false) s₂.mem := by rw [m₂]; exact hS₀
    refine WP.seq (WP.mono (rest_okF hp (q := 0) (by omega_using [hlt]) M) fun st' ⟨M', hf'⟩ => ?_)
    refine WP.mono (tailL_ok hp ctr cf gh gf M' (hS₂.slots hf' M'.kept)) fun st h => h.congr fun d _ _ => ?_
    simp only [show ¬ 2 ≤ n s by omega_using [hlt], decide_false, Bool.false_and]
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · refine WP.seq (WP.mono (cmpMin_ok (s := s) false (by rw [g₂]; exact hg _ (by decide)))
      fun s₃ ⟨g₃, m₃, rd₃, wr₃, cf₃⟩ => ?_)
    refine WP.ite (decide (n s < smallMin false)) (by simp only [eval, cf₃]) (fun h0 => ?_) (fun h0 => ?_)
    · exact cl (by simpa [smallMin] using h0) s₃ (g₃.trans g₂) (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂)
    · exact pc s₃ (by simp [smallMin] at h0; omega_using [h0]) (g₃.trans g₂) (m₃.trans m₂) (rd₃.trans rd₂)
        (wr₃.trans wr₂)
  · exact pc s₂ (by simp at h; omega_using [h]) g₂ m₂ rd₂ wr₂

/-- `vg_aes_gcm_encrypt_blocks` with loops on all the blocks from 2 on that
leave `PieceL ℓ zf`, and calls that need no working space: what is left in
`scratch`. -/
theorem encryptR_leaves (ctr : Ctr32Impl) (cf : Ctr32Free ctr.callee) (gh : GhashImpl) (gf : GhashFree gh.fn.code)
    {aligned : Bool} {piece : Prog isa} {ℓ : Nat} {zf : Nat → Nat → Bool} (hℓ : ℓ ≤ 1024)
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ 1 →
      WP isa piece s₃ fun s₄ => Gcm.X86_64.Stitch.EPost s₃ s₄ ∧ Gcm.X86_64.Stitch.PieceL ℓ zf s₃ s₄) :
    WP isa (encrypt ⟨ctr.callee.name, ctr.callee.code⟩ gh.fn (some piece) aligned true true false (some piece)) s
      fun s' => Scr s 0 (fun d => decide (2 ≤ n s) && (decide (AlignedScratch.offset aligned (S s) ≤ d) &&
        decide (d < AlignedScratch.offset aligned (S s) + ℓ) &&
        zf (n s) (d - AlignedScratch.offset aligned (S s)))) s'.mem :=
  WP.seq (WP.mono (entry_ok hp) fun _ ⟨h11, hg, hk, hf, hrd, hwr⟩ =>
    fullBodyL_ok hp hpiece (by have := AlignedScratch.offset_bounds aligned (S s); omega_using [hℓ, this])
      ctr cf gh gf h11 hg hk hf hrd hwr)

end

end VG.Proof.AesGcm.X86_64.Blocks
