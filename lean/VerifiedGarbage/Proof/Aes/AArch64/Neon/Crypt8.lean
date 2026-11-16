module

public import VerifiedGarbage.Proof.Aes.AArch64.Neon.Layers
public import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Encrypting and decrypting eight blocks, bitsliced in AdvSIMD registers, on AArch64

`encrypt8_ok` and `decrypt8_ok`: from eight blocks in the registers `A j`
(`InRel`), with the bitsliced round keys in the scratch buffer (`KeysAt`),
`encrypt8` and `decrypt8` leave the eight results in the registers `B j`,
having written only the first 96 bytes of the scratch buffer and the
registers `x6`, `x7`, `kp` and `cnt`. The layers are composed from their
proofs (`Layers.lean`), as `Encrypt.lean` and `Decrypt.lean` compose those
of four blocks; the round loops' invariants are the specification's `foldl`
over the rounds done.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Neon

open VG VG.AArch64 VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.AArch64.StraightV (vAddr)
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher invCipher)

/-- The words of the state registers. -/
abbrev QA (s : State) (i : Nat) : BitVec 128 := s.v (A i)
abbrev QB (s : State) (i : Nat) : BitVec 128 := s.v (B i)

/-- The bitsliced round keys `0 … R` of the schedule `w`, from byte 128 of
the scratch buffer at `b`, 128 bytes each. -/
def KeysAt (m : Mem) (b : Addr) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel (fun k => m.readW (vAddr (b + BitVec.ofNat 64 (128 + 128 * j)) k) 128)
    (roundKey w j)

/-- What the eight blocks need: the scratch buffer (2048 bytes at `sb`, `ScrIn`) is
writable, the round keys are in it, and `x1` is the number of rounds. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : ScrIn (s₀.gpr sb) s₀.wr
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x1 : s₀.gpr .x1 = BitVec.ofNat 64 R
  keys : KeysAt s₀.mem (s₀.gpr sb) R w

/-- What stays the same. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → r ≠ cnt → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 96⟩] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb :=
  hc.keep _ (by decide) (by decide) (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hk : Keeps s s') : Ctx s₀ s' :=
  ⟨hk.rd.trans hc.rd, hk.wr.trans hc.wr, hk.sp.trans hc.sp,
    fun r h6 h7 hkp hcn => (hk.gpr r h6 h7).trans (hc.keep r h6 h7 hkp hcn),
    hc.frame.trans (by rw [← hc.base]; exact hk.frame)⟩

theorem Ctx.scr {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) :
    ScrIn (s.gpr sb) s.wr := by
  rw [hc.base, hc.wr]; exact hp.scr

theorem keyRel_congr {K K' : Nat → BitVec 128} {rk : List Byte} (h : KeyRel K rk)
    (he : ∀ k < 8, K' k = K k) : KeyRel K' rk := by
  intro b hb i hi
  rw [← h b hb i hi]
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, he j hj]

theorem key_addr (b : Addr) (n k : Nat) :
    vAddr (b + BitVec.ofNat 64 n) k = b + BitVec.ofNat 64 (n + 16 * k) := by
  simp only [vAddr]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) :
    KeysAt s.mem (s₀.gpr sb) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  simp only [key_addr]
  exact hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 96, 1952⟩)
    (Offset.contains _ (by omega_using []) (by omega_using [hR, hj, hk]) (by omega_using []))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_using []) (by omega_using []))
    (by decide)

theorem ark_ok {s : State} {b : Addr} {n : Nat} (hscr : ScrIn b s.wr)
    (hk : s.gpr kp = b + BitVec.ofNat 64 n) (hn : n + 128 ≤ 2048) : StraightQ.Ok arkCfg s := by
  obtain ⟨L, hL, _, hscr⟩ := hscr
  intro k hk'
  simp only [arkCfg] at hk'
  refine ⟨⟨b, L⟩, List.mem_append_right _ hscr, ?_⟩
  show Region.Contains _ (vAddr (s.gpr kp) k) 16
  rw [hk, key_addr]
  exact Offset.contains_base b (by omega_using [hn, hk', hL]) (by omega_using [hn, hk'])

/-! ## One layer at a time -/

/-- A layer keeps `Ctx`, `kp` and `cnt`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ Keeps s s') (hc : Ctx s₀ s)
    (hQ : ∀ s', Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → s'.gpr cnt = s.gpr cnt → Q s') :
    WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hk⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.step hk) hP (hk.gpr kp (by decide) (by decide))
    (hk.gpr cnt (by decide) (by decide))⟩

theorem layer_wp' {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : WP isa (.block is) s fun s' => P s' ∧ Keeps s s') (hc : Ctx s₀ s)
    (hQ : ∀ s', Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → s'.gpr cnt = s.gpr cnt → Q s') :
    WP isa (.block is) s Q :=
  WP.mono hl fun s' ⟨hP, hk⟩ => hQ s' (hc.step hk) hP (hk.gpr kp (by decide) (by decide))
    (hk.gpr cnt (by decide) (by decide))

/-- An instruction that writes `kp` or `cnt`, before the rest of its block. -/
theorem gpr_wp {s₀ s : State} {i : Instr} {is : List Instr} {d : Reg} {v : BitVec 64}
    {P : State → Prop} (he : exec i s = some (s.write .x d v)) (hc : Ctx s₀ s)
    (hd : d = kp ∨ d = cnt)
    (h : ∀ s', Ctx s₀ s' → s'.gpr d = v → (∀ r, r ≠ d → s'.gpr r = s.gpr r) → s'.v = s.v →
      s'.mem = s.mem → WP isa (.block is) s' P) :
    WP isa (.block (i :: is)) s P := by
  rw [WP.block_cons_iff]
  refine ⟨_, he, h _ ⟨hc.rd, hc.wr, hc.sp, fun r h6 h7 hkp hcn => ?_, hc.frame⟩ ?_ ?_ rfl rfl⟩
  · have hr : r ≠ d := by rcases hd with rfl | rfl <;> with_reducible assumption
    simp only [State.write, hr, ite_false]
    exact hc.keep r h6 h7 hkp hcn
  · simp [State.write]
  · intro r hr; simp [State.write, hr]

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp [State.read]

theorem ofNat_ne_zero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k != 0) = !decide (k = 0) := by
  have : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    bv_omega
  rw [bne, this]

theorem eval_cnt {s : State} {k : Nat} (h : s.gpr cnt = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    AArch64.eval (.nonzero .x cnt) s = some (!decide (k = 0)) := by
  simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, h, ofNat_ne_zero hk]

theorem qa_congr {s s' : State} (h : s'.v = s.v) : QA s' = QA s := by
  funext i; show s'.v (A i) = s.v (A i); rw [h]

/-! ## The rounds -/

theorem kp_step (b : Addr) (m : Nat) :
    b + BitVec.ofNat 64 (128 + 128 * m) + BitVec.ofNat 64 128 =
      b + BitVec.ofNat 64 (128 + 128 * (m + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 128 + 128 * m + 128 = 128 + 128 * (m + 1) by omega_using []]

/-- AddRoundKey with round key `j`, when `kp` is at it. -/
theorem ark_step {P : Nat → VReg}
    (hchk : StraightQ.check (lanes 128 11) arkCfg (StraightQ.linExt 8) (Impl.Aes.AArch64.Neon.addRoundKey P)
      (StraightQ.linEnv (insOf P) []) (StraightQ.linPost 11 (outsOf P arkG)) = true)
    {s₀ s : State} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * j)) (hj : j ≤ R)
    (hbs : BsRel (fun i => s.v (P i)) T) {Q : State → Prop}
    (h : ∀ s', Ctx s₀ s' → s'.gpr kp = s.gpr kp → s'.gpr cnt = s.gpr cnt →
      BsRel (fun i => s'.v (P i)) (fun b => addRoundKey (T b) (roundKey w j)) → Q s') :
    WP isa (.block (Impl.Aes.AArch64.Neon.addRoundKey P)) s Q := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have hok : StraightQ.Ok arkCfg s := ark_ok (b := s₀.gpr sb) (by rw [hc.wr]; exact hp.scr) hk
    (by omega_using [hR, hj])
  have hkey : KeyRel (keyWord s) (roundKey w j) := by
    have := hp.keysAt hc j hj
    show KeyRel (fun k => s.mem.readW (vAddr (s.gpr kp) k) 128) _
    rw [hk]; exact this
  refine layer_wp (addRoundKey_ok hchk hok) hc fun s' hc' h' hk' hn' => h s' hc' hk' hn' ?_
  exact bs_addRoundKey h' hbs hkey

/-- A middle round. -/
theorem round_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * m))
    (hn : s.gpr cnt = BitVec.ofNat 64 (R - 1 - m)) (hm : m + 1 < R) (hbs : BsRel (QA s) T) :
    WP isa (.block roundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * (m + 1)) ∧
      s'.gpr cnt = BitVec.ofNat 64 (R - 1 - (m + 1)) ∧
      BsRel (QA s') (fun b => rnd w (m + 1) (T b)) := by
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine gpr_wp (exec_addImm_x (by decide)) hc (.inl rfl) fun s₁ hc₁ hk₁ ho₁ hv₁ _ => WP.block_nil ?_
  rw [read_x, hk, kp_step] at hk₁
  have hbs₁ : BsRel (QA s₁) T := by rw [qa_congr hv₁]; exact hbs
  refine layer_wp (sbox_ok (hc₁.scr hp)) hc₁ fun s₂ hc₂ h₂ hk₂ hn₂ => ?_
  have hbs₂ := bs_subBytes h₂ hbs₁
  refine layer_wp' (shiftRows_wp s₂) hc₂ fun s₃ hc₃ h₃ hk₃ hn₃ => ?_
  have hbs₃ := bs_shiftRows h₃ hbs₂
  refine layer_wp' (mixColumns_wp s₃) hc₃ fun s₄ hc₄ h₄ hk₄ hn₄ => ?_
  have hbs₄ := bs_mixColumns h₄ hbs₃
  refine ark_step arkA_check hp hc₄ (j := m + 1) (by rw [hk₄, hk₃, hk₂, hk₁]) (by omega_using [hm])
    hbs₄ fun s₅ hc₅ hk₅ hn₅ hbs₅ => ?_
  refine gpr_wp (exec_subImm_x (by decide)) hc₅ (.inr rfl) fun s₆ hc₆ hn₆ ho₆ hv₆ _ =>
    WP.block_nil ⟨hc₆, ?_, ?_, ?_⟩
  · rw [ho₆ kp (by decide), hk₅, hk₄, hk₃, hk₂, hk₁]
  · rw [hn₆, read_x, hn₅, hn₄, hn₃, hn₂, ho₁ cnt (by decide), hn,
      Offset.ofNat_sub_ofNat (by omega_using [hm]), Nat.sub_sub (R - 1) m 1]
  · rw [qa_congr hv₆]; exact hbs₅

/-- Eight blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt8_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (QA s₀) S) :
    WP isa encrypt8 s₀ fun s => Ctx s₀ s ∧ InRel (QB s) (fun b => cipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega_using [h]
  let K : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * m) ∧
    s.gpr cnt = BitVec.ofNat 64 (R - 1 - m) ∧ BsRel (QA s) (fun b => midRounds w m (K b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * (R - 1)) ∧
    BsRel (QA s) (fun b => midRounds w (R - 1) (K b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- `ortho`, the first round key.
    rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
    refine layer_wp (ortho_ok orthoA_check (by decide) (by decide +kernel) s₀) (Ctx.refl s₀)
      fun s₁ hc₁ h₁ _ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine gpr_wp (exec_addImm_x (by decide)) hc₁ (.inl rfl) fun s₂ hc₂ hk₂ ho₂ hv₂ _ => ?_
    refine gpr_wp (exec_subImm_x (by decide)) hc₂ (.inr rfl) fun s₃ hc₃ hn₃ ho₃ hv₃ _ =>
      WP.block_nil ?_
    have hk₃ : s₃.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * 0) := by
      rw [ho₃ kp (by decide), hk₂, read_x, hc₁.base]
    have hn₃' : s₃.gpr cnt = BitVec.ofNat 64 (R - 1) := by
      rw [hn₃, read_x, ho₂ .x1 (by decide), hc₁.keep .x1 (by decide) (by decide) (by decide) (by decide),
        hp.x1, Offset.ofNat_sub_ofNat (by omega_using [hR1])]
    have hbs₃ : BsRel (QA s₃) S := by rw [qa_congr hv₃, qa_congr hv₂]; exact hbs₁
    exact ark_step arkA_check hp hc₃ hk₃ (Nat.zero_le R) hbs₃ fun s₄ hc₄ hk₄ hn₄ hbs₄ =>
      ⟨0, by omega_using [], by omega_using [hR1], hc₄, by rw [hk₄, hk₃], by rw [hn₄, hn₃', Nat.sub_zero], hbs₄⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hn, hbs⟩ := hs
    refine WP.mono (round_ok hp hc hk hn hm hbs) fun s' ⟨hc', hk', hn', hbs'⟩ => ?_
    have hz := eval_cnt hn' (by omega_using [hR])
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [show R - 1 - (m + 1) = 0 by omega_using [hlast]]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega_using [hlast]
      · rw [show R - 1 = m + 1 by omega_using [hlast]]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [midRounds_succ]
    · refine .inr ⟨hz.trans (by simp [show R - 1 - (m + 1) ≠ 0 by omega_using [hlast, hm]]),
        R - 1 - (m + 1), by omega_using [hm], m + 1, rfl, by omega_using [hlast, hm], hc', hk', hn',
        fun b hb i hi => by rw [hbs' b hb i hi]; simp only [midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine gpr_wp (exec_addImm_x (by decide)) hc (.inl rfl) fun s₁ hc₁ hk₁ _ hv₁ _ => WP.block_nil ?_
    rw [read_x, hk, kp_step, show R - 1 + 1 = R by omega_using [hR1]] at hk₁
    have hbs₁ : BsRel (QA s₁) (fun b => midRounds w (R - 1) (K b)) := by rw [qa_congr hv₁]; exact hbs
    refine layer_wp (sbox_ok (hc₁.scr hp)) hc₁ fun s₂ hc₂ h₂ hk₂ _ => ?_
    have hbs₂ := bs_subBytes h₂ hbs₁
    refine layer_wp' (shiftRows_wp s₂) hc₂ fun s₃ hc₃ h₃ hk₃ _ => ?_
    have hbs₃ := bs_shiftRows h₃ hbs₂
    refine ark_step arkB_check hp hc₃ (j := R) (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃
      fun s₄ hc₄ _ _ hbs₄ => ?_
    refine layer_wp (ortho_ok orthoB_check (by decide) (by decide +kernel) s₄) hc₄
      fun s₅ hc₅ h₅ _ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [cipher_eq]; rfl

/-! ## The inverse cipher -/

theorem kp_back (b : Addr) {k : Nat} (hk : 0 < k) :
    b + BitVec.ofNat 64 (128 + 128 * k) - BitVec.ofNat 64 128 =
      b + BitVec.ofNat 64 (128 + 128 * (k - 1)) := by
  rw [Offset.add_ofNat_sub b (by omega_using []),
    show 128 + 128 * k - 128 = 128 + 128 * (k - 1) by omega_using [hk]]

theorem exec_lsl_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp [reduceExec, Size.bits, h]

theorem shl7 : ∀ R ≤ 14, BitVec.ofNat 64 R <<< 7 = BitVec.ofNat 64 (128 * R) := by decide

/-- A middle round of the inverse cipher. -/
theorem invRound_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hc : Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * (R - m)))
    (hn : s.gpr cnt = BitVec.ofNat 64 (R - 1 - m)) (hm : m + 1 < R) (hbs : BsRel (QA s) T) :
    WP isa (.block invRoundBody) s fun s' => Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * (R - (m + 1))) ∧
      s'.gpr cnt = BitVec.ofNat 64 (R - 1 - (m + 1)) ∧
      BsRel (QA s') (fun b => irnd R w m (T b)) := by
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine gpr_wp (exec_subImm_x (by decide)) hc (.inl rfl) fun s₁ hc₁ hk₁ ho₁ hv₁ _ => WP.block_nil ?_
  rw [read_x, hk, kp_back _ (by omega_using [hm]), show R - m - 1 = R - (m + 1) by omega_using []] at hk₁
  have hbs₁ : BsRel (QA s₁) T := by rw [qa_congr hv₁]; exact hbs
  refine layer_wp' (invShiftRows_wp s₁) hc₁ fun s₂ hc₂ h₂ hk₂ hn₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine layer_wp (invSbox_ok (hc₂.scr hp)) hc₂ fun s₃ hc₃ h₃ hk₃ hn₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine ark_step arkB_check hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega_using [])
    hbs₃ fun s₄ hc₄ hk₄ hn₄ hbs₄ => ?_
  refine layer_wp' (invMixColumns_wp s₄) hc₄ fun s₅ hc₅ h₅ hk₅ hn₅ => ?_
  have hbs₅ := bs_invMixColumns h₅ hbs₄
  refine gpr_wp (exec_subImm_x (by decide)) hc₅ (.inr rfl) fun s₆ hc₆ hn₆ ho₆ hv₆ _ =>
    WP.block_nil ⟨hc₆, ?_, ?_, ?_⟩
  · rw [ho₆ kp (by decide), hk₅, hk₄, hk₃, hk₂, hk₁]
  · rw [hn₆, read_x, hn₅, hn₄, hn₃, hn₂, ho₁ cnt (by decide), hn,
      Offset.ofNat_sub_ofNat (by omega_using [hm]), Nat.sub_sub (R - 1) m 1]
  · rw [qa_congr hv₆]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega_using []]

/-- Eight blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt8_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (QA s₀) S) :
    WP isa decrypt8 s₀ fun s => Ctx s₀ s ∧ InRel (QB s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega_using [h]
  let K : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * (R - m)) ∧
    s.gpr cnt = BitVec.ofNat 64 (R - 1 - m) ∧ BsRel (QA s) (fun b => invMid R w m (K b))
  let Mid : State → Prop := fun s => Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * 1) ∧
    BsRel (QA s) (fun b => invMid R w (R - 1) (K b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- `ortho`, the last round key.
    rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
    refine layer_wp (ortho_ok orthoA_check (by decide) (by decide +kernel) s₀) (Ctx.refl s₀)
      fun s₁ hc₁ h₁ _ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    have hx1 : s₁.gpr .x1 = BitVec.ofNat 64 R := by
      rw [hc₁.keep .x1 (by decide) (by decide) (by decide) (by decide), hp.x1]
    refine gpr_wp (exec_lsl_x (by decide)) hc₁ (.inl rfl) fun s₂ hc₂ hk₂ ho₂ hv₂ _ => ?_
    refine gpr_wp exec_add hc₂ (.inl rfl) fun s₃ hc₃ hk₃ ho₃ hv₃ _ => ?_
    refine gpr_wp (exec_addImm_x (by decide)) hc₃ (.inl rfl) fun s₄ hc₄ hk₄ ho₄ hv₄ _ => ?_
    refine gpr_wp (exec_subImm_x (by decide)) hc₄ (.inr rfl) fun s₅ hc₅ hn₅ ho₅ hv₅ _ =>
      WP.block_nil ?_
    have hk₅ : s₅.gpr kp = s₀.gpr sb + BitVec.ofNat 64 (128 + 128 * R) := by
      rw [ho₅ kp (by decide), hk₄, read_x, hk₃, read_x, read_x, hk₂, read_x, hx1,
        ho₂ sb (by decide), hc₁.base, shl7 R hR, BitVec.add_comm (BitVec.ofNat 64 (128 * R)),
        BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm (128 * R) 128]
    have hn₅' : s₅.gpr cnt = BitVec.ofNat 64 (R - 1) := by
      rw [hn₅, read_x, ho₄ .x1 (by decide), ho₃ .x1 (by decide), ho₂ .x1 (by decide), hx1,
        Offset.ofNat_sub_ofNat (by omega_using [hR1])]
    have hbs₅ : BsRel (QA s₅) S := by
      rw [qa_congr hv₅, qa_congr hv₄, qa_congr hv₃, qa_congr hv₂]; exact hbs₁
    exact ark_step arkA_check hp hc₅ hk₅ (Nat.le_refl R) hbs₅ fun s₆ hc₆ hk₆ hn₆ hbs₆ =>
      ⟨0, by omega_using [], by omega_using [hR1], hc₆, by rw [hk₆, hk₅, Nat.sub_zero],
        by rw [hn₆, hn₅', Nat.sub_zero], hbs₆⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hn, hbs⟩ := hs
    refine WP.mono (invRound_ok hp hc hk hn hm hbs) fun s' ⟨hc', hk', hn', hbs'⟩ => ?_
    have hz := eval_cnt hn' (by omega_using [hR])
    by_cases hlast : m + 2 = R
    · refine .inl ⟨hz.trans (by simp [show R - 1 - (m + 1) = 0 by omega_using [hlast]]), hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega_using [hlast]
      · rw [show R - 1 = m + 1 by omega_using [hlast]]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨hz.trans (by simp [show R - 1 - (m + 1) ≠ 0 by omega_using [hlast, hm]]),
        R - 1 - (m + 1), by omega_using [hm], m + 1, rfl, by omega_using [hlast, hm], hc', hk', hn',
        fun b hb i hi => by rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [invLastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine gpr_wp (exec_subImm_x (by decide)) hc (.inl rfl) fun s₁ hc₁ hk₁ _ hv₁ _ => WP.block_nil ?_
    rw [read_x, hk, kp_back _ (by decide)] at hk₁
    have hbs₁ : BsRel (QA s₁) (fun b => invMid R w (R - 1) (K b)) := by rw [qa_congr hv₁]; exact hbs
    refine layer_wp' (invShiftRows_wp s₁) hc₁ fun s₂ hc₂ h₂ hk₂ _ => ?_
    have hbs₂ := bs_invShiftRows h₂ hbs₁
    refine layer_wp (invSbox_ok (hc₂.scr hp)) hc₂ fun s₃ hc₃ h₃ hk₃ _ => ?_
    have hbs₃ := bs_invSubBytes h₃ hbs₂
    refine ark_step arkB_check hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃
      fun s₄ hc₄ _ _ hbs₄ => ?_
    refine layer_wp (ortho_ok orthoB_check (by decide) (by decide +kernel) s₄) hc₄
      fun s₅ hc₅ h₅ _ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.AArch64.Neon
