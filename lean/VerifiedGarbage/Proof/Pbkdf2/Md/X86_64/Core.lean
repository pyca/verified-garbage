import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Framework.X86_64.Depth

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Pbkdf2`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`, correct

`pbkdf2` saves our caller's registers, makes the key (hashing a password
longer than a block), HMAC's states for it and the inner state after the salt;
then each block `i` of the output is `U₁` (`update` with `INT (i)` and HMAC's
`finalize`), `iterate` from it, and as much of `T_i` as the output still
needs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-! ## The entry -/

omit hp hz in
/-- After `scratch` is loaded. -/
structure Loaded (s₀ s : State) : Prop where
  r8 : s.gpr .r8 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀
  r10 : s.gpr .r10 = s₀.gpr .r8
  other : ∀ r, r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hz in
theorem loadScr_ok : WP isa (.block Hash.loadScr) s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Loaded s₀) := by
  simp only [Hash.loadScr]
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 16) (by rw [ea_nat, u₁.other _ (by decide)]) ?_
    fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁.rd, u₁.wr, hp.rd]
    exact ⟨argR s₀, by simp, show (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Contains _ 8 from
      Offset.contains _ (by decide) (by decide) (by decide)⟩
  · rw [u₂.gpr, u₁.mem]; rfl
  · rw [u₂.other _ (by decide), u₁.gpr]
  · intro r h₁ h₂; rw [u₂.other r h₁, u₁.other r h₂]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem entry_ok {s₂ : State} (hl₂ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Loaded s₀ s₂) : WP isa (.block H.entry) s₂ fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s ∧
    s.gpr .rbx = pw s₀ ∧ s.gpr .rbp = s₀.gpr .rsi ∧ s.gpr .r12 = salt s₀ ∧ s.gpr .r13 = s₀.gpr .rcx ∧
    s.cf = some (decide (pwl s₀ < H.P.B + 1)) := by
  have hW := hz.W
  have := hp.snw; have hc0 := hp.c0
  have hS : H.S = H.P.N + H.P.B := rfl
  simp only [Hash.entry]
  have h8 : s₂.gpr .r8 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀ := hl₂.r8
  have g₂ : ∀ r, r ≠ .r8 → r ≠ .r10 → s₂.gpr r = s₀.gpr r := hl₂.other
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.save_ok H.hh h8 hW (L := (H.W + H.S) * 8)
    (by rw [hl₂.wr]; exact sc_mem hp) (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)
    fun s₃ g₃ rd₃ wr₃ f₃ sv₃ => ?_
  refine wp_mov fun s₄ u₄ _ _ => ?_
  have h15 : s₄.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀ := by rw [u₄.gpr, g₃, h8]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, hl₂.wr]
  refine wp_store (a := A s₀ H.outO) (by rw [ea_nat, h15]) (in_sc hp hz wr₄ (by exact hz.o_outO_8_le_L))
    fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_mov32r fun s₆ u₆ => wp_subi fun s₇ u₇ _ => ?_
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, wr₅, wr₄]
  have h15' : s₆.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀ := by rw [u₆.other _ (by decide), g₅, h15]
  refine wp_store (a := A s₀ H.cO) (by rw [ea_nat, u₇.other _ (by decide), h15'])
    (by rw [u₇.wr, wr₆]; exact in_sc hp hz rfl (by exact hz.o_cO_8_le_L)) fun s₈ g₈ m₈ rd₈ wr₈ => ?_
  refine wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => wp_mov fun s₁₁ u₁₁ _ _ =>
    wp_mov fun s₁₂ u₁₂ _ _ => wp_cmpi fun s₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ c₁₃ _ => WP.block_nil ?_
  -- The registers.
  have g : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r8 → r ≠ .r10 →
      s₁₃.gpr r = s₀.gpr r := fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => by
    rw [g₁₃, u₁₂.other r h₆, u₁₁.other r h₅, u₁₀.other r h₄, u₉.other r h₃, g₈, u₇.other r h₁, u₆.other r h₁,
      g₅, u₄.other r h₂, g₃, g₂ r h₇ h₈]
  have gs : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₈.gpr r = s₂.gpr r :=
    fun r h₁ h₂ _ _ _ _ => by rw [g₈, u₇.other r h₁, u₆.other r h₁, g₅, u₄.other r h₂, g₃]
  have rax₈ : s₇.gpr .rax = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₇.gpr, u₆.gpr, g₅, u₄.other _ (by decide), g₃, hl₂.r10, zx32, sx1,
      ofNat_pred hc0]
  have r9₄ : s₄.gpr .r9 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  have m₁₃ : s₁₃.mem = (s₃.mem.writeW (A s₀ H.outO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1)) := by
    rw [m₁₃, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈, u₇.mem, u₆.mem, m₅, u₄.mem, r9₄, rax₈]
  have dOC : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ := part_disj hz (Or.inl (by exact hz.o_outO_8_le_cO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_cO_8_le_L)
  have fW : Frame [sR s₀ H.outO 16] s₃.mem s₁₃.mem := by
    rw [m₁₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by exact hz.o_outO_64d8_le_outO_16)
      (by exact hz.o_outO_16_lt_p64))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_cO) (by exact hz.o_cO_64d8_le_outO_16) (by exact hz.o_outO_16_lt_p64))
  have f₀ : Frame [VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀] s₀.mem s₁₃.mem := by
    have e₂ : s₂.mem = s₀.mem := hl₂.mem
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, by simp, part_sub (by exact hz.o_outO_16_le_L)⟩
  have sv : SavedRegs H.hh (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.rbx, g₂ _ (by decide) (by decide)], by rw [sv₃.rbp, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r12, g₂ _ (by decide) (by decide)], by rw [sv₃.r13, g₂ _ (by decide) (by decide)],
      by rw [sv₃.r14, g₂ _ (by decide) (by decide)], by rw [sv₃.r15, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [rd₁₃, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈, u₇.rd, u₆.rd, rd₅, u₄.rd, rd₃, hl₂.rd],
    by rw [wr₁₃, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈, u₇.wr, wr₆],
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈, u₇.other _ (by decide), h15'],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 48) (Or.inl (by exact hz.o_W8_48_le_outO)) (by exact hz.o_W8_48_le_L) (by exact hz.o_outO_16_le_L),
    by rw [m₁₃, readW_writeW_ne _ _ dOC, Mem.readW_writeW_self64],
    by rw [m₁₃, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [g₁₃, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide)]
  · rw [c₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      gs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide), sx_ofNat (by exact hz.o_B_1_lt_p31), toNat_ofNat_lt (by exact hz.o_B_1_lt_p64)]

/-! ## Helpers -/

omit hp hz in
theorem KR.same {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) (hm : s'.mem = s.mem) :
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h) (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ≠ .r15 ∧ d ≠ .rsp) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s' :=
  h.same u.rd u.wr (u.other _ hd.2.symm) (u.other _ hd.1.symm) u.mem

omit hp hz in
/-- `d ← scratch + o`. -/
theorem scr_ok {s : State} {d : Reg} (h15 : s.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) {o : Nat} (ho : o < 2 ^ 31)
    {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' d (A s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, h15, sx_ofNat ho]

omit hp hz in
theorem stk_sub {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below (s.gpr .rsp) n) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀) := by
  rw [h.rsp]; exact below_stk hn

omit hz in
theorem stk_sc {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {n : Nat} (hn : n ≤ 24) {R : Region}
    (hR : Region.Sub R (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀)) : (below (s.gpr .rsp) n).Disjoint R :=
  (hp.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sub h hn)).sub_right hR

omit hz in
theorem in_wr {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

omit hz in
/-- The parts of `scratch` the functions we call get, as covered regions. -/
theorem cov_part {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (VG.Proof.Pbkdf2.Md.X86_64.Pbk.in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (VG.Proof.Pbkdf2.Md.X86_64.Pbk.in_wr hp h) hn

/-! ## The key -/

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

omit hp hz in
theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.hDN; omega

omit hp hz in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hl := VG.Proof.Pbkdf2.Md.X86_64.Pbk.hash_len hH k; have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega))]

omit hp hz in
theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  have hB := hH.hB; have := hH.hDL
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.hash_len]; omega
  · omega

omit hp hz in
/-- What the entry sets up, kept until the salt is absorbed. -/
structure KE (s₀ s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s
  rbx : s.gpr .rbx = pw s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = salt s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

omit hp hz in
theorem KE.upd {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, by rw [u.other _ (ne _ (by simp)), h.rbx],
    by rw [u.other _ (ne _ (by simp)), h.rbp], by rw [u.other _ (ne _ (by simp)), h.r12],
    by rw [u.other _ (ne _ (by simp)), h.r13]⟩

theorem KE.call {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz hrd hwr hcs hn hf hw, by rw [hcs _ (by simp [calleeSaved]), h.rbx],
    by rw [hcs _ (by simp [calleeSaved]), h.rbp], by rw [hcs _ (by simp [calleeSaved]), h.r12],
    by rw [hcs _ (by simp [calleeSaved]), h.r13]⟩

/-! ### Hashing a password longer than a block -/

omit hp in
theorem hk1_ok {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)) s fun t =>
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO := by
  have hB := hz.z.B_le
  have hD := hz.z.D
  rw [← List.append_nil (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)]
  exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), u₁.gpr⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (hdi : s.gpr .rdi = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  exact VG.Proof.Pbkdf2.Md.X86_64.Calls.init_call hH.stream (st := A s₀ H.stWO) hdi
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp h.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))) fun s₂ a₂ r₂ =>
      ⟨h.call hp hz a₂.rd a₂.wr a₂.cs (by decide) a₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (pwl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbx]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbp]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₇.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp k₇.kr (by exact hz.o_stWO_hsS_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp k₇.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.pw_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₇.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := (hp.stk_pw.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sub k₇.kr (by decide)))
      stk_sc := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₇.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (pwl s₀))
    (hsi : s.gpr .rsi = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua (by have := hp.pwnw; omega) fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈.rd a₈.wr a₈.cs (by decide) a₈.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · have := r₈ [] hr hsi
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) s fun t =>
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) ∧
      t.gpr .rsi = s₀.gpr .rsi ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ _ _ => ?_
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]) (by exact hz.o_hkO_lt_p31)
    fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  have k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.rbp], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { rdi := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
      rdx := by rw [u₁₂.other _ (by decide), u₁₁.gpr]
      rcx := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.kr.r15]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp k₁₂.kr (by exact hz.o_stWO_hsS_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp k₁₂.kr (by rw [hF]; exact hz.o_hkO_N_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp k₁₂.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L) (by rw [hF]; exact hz.o_hkO_N_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by rw [hF]; exact hz.o_hkO_N_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      stk_st := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₁₂.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₁₂.kr (by decide) (part_sub (by rw [hF]; exact hz.o_hkO_N_le_L))
      stk_sc := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₁₂.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀))
    (hsi : s.gpr .rsi = s₀.gpr .rsi) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃.rd a₁₃.wr a₁₃.cs (by decide) a₁₃.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by rw [hF]; exact hz.o_hkO_N_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · rw [bytesAt_take _ _ hD.2.1]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .rsi).isLt)
      (by rw [hsi, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) s fun t =>
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧ t.mem = s.mem := by
  have hD := hz.z.D; have hN := hz.z.N
  have hB := hz.z.B_le
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok h.kr.r15 (by exact hz.o_hkO_lt_p31) fun s₁₄ u₁₄ => wp_mov32i fun s₁₅ u₁₅ _ _ => WP.block_nil ?_
  exact ⟨(h.upd u₁₄ (by decide)).upd u₁₅ (by decide), by rw [u₁₅.other _ (by decide), u₁₄.gpr],
    by rw [u₁₅.gpr, zx_ofNat (by exact hz.o_D_lt_p32), toNat_ofNat_lt (by exact hz.o_D_lt_p64)], by rw [u₁₅.mem, u₁₄.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ t.gpr .rdx = A s₀ H.hkO ∧ (t.gpr .rcx).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

omit hp hz in
/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
omit hp hz in
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

theorem key_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s)
    (hcf : s.cf = some (decide (pwl s₀ < H.P.B + 1))) :
    WP isa H.key s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ t.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ ∧ (t.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ ∧
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀) := by
  have hD := hz.z.D
  unfold Hash.key
  refine WP.ite (!decide (pwl s₀ < H.P.B + 1)) (by simp [eval, hcf]) (fun hT => ?_) fun hF => ?_
  · have hlong : ¬ pwl s₀ < H.P.B + 1 := of_decide_eq_false (Bool.not_eq_true' _ ▸ hT)
    have e₁ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    have e₂ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hlong)
    rw [e₁, e₂]
    refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hashKey_ok hp hz hH h) fun t ⟨k, rdx, rcx, hb⟩ =>
      ⟨k, rdx, rcx, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
    rw [hb, VG.Proof.Pbkdf2.Md.X86_64.Pbk.blockKey_hash hH (by rw [bytesAt_length]; omega)]
  · have hshort : pwl s₀ < H.P.B + 1 := of_decide_eq_true (by simpa using hF)
    have e₁ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    have e₂ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hshort)
    rw [e₁, e₂]
    refine wp_mov fun t₁ u₁ _ _ => wp_mov fun t₂ u₂ _ _ => WP.block_nil ?_
    refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.rbx],
      by rw [u₂.gpr, u₁.other _ (by decide), h.rbp], ⟨.inl ⟨rfl, rfl⟩, by omega, ?_⟩⟩
    rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

/-! ## HMAC's states -/

omit hp hz in
theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega) hi) hr

omit hp hz in
/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (VG.WriteBytes.writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ m' := by
  exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by exact hz.o_st0O_S_le_st0O_3mS))) h.i,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_st0O_3mS))) h.o,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_st0O_3mS))) h.s⟩

omit hz in
/-- Regions a call writes, disjoint from a part of `scratch`. -/
theorem disj_call {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {X : Region} (hX : Region.Sub X (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀))
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hw : ∀ r ∈ ws, X.Disjoint r) :
    ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp h hn hX).symm

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ m kp kl) {s : State}
    (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below (s.gpr .rsp) 24).Disjoint ⟨kp, kl⟩ := by
  have hD := hz.z.D; have hN := hz.z.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by exact hz.o_st0O_S_le_L)), hp.pw_s.sub_right (part_sub (by exact hz.o_st1O_S_le_L)),
      hp.pw_s.sub_right low_sub, hp.stk_pw.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sub h (Nat.le_refl _))⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by exact hz.o_st0O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st0O_S_le_L),
      part_disj hz (Or.inr (by exact hz.o_st1O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st1O_S_le_L), low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp h (Nat.le_refl _) (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (hdx : s.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀)
    (hcx : (s.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀) (hk : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀)) :
    WP isa (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.st0O ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rsi H.st1O ++
      ([.mov .r8 (.reg .r15)] : List Instr))) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀) ∧
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok h.kr.r15 (by exact hz.o_st0O_lt_p31) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok (by rw [u₁.other _ (by decide), h.kr.r15]) (by exact hz.o_st1O_lt_p31) fun s₂ u₂ => wp_mov fun s₃ u₃ _ _ =>
    WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { rdi := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdx]
      rcx := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
      r8 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r15]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp k₃.kr (by exact hz.o_st0O_S_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp k₃.kr (by exact hz.o_st1O_S_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp k₃.kr (by exact hz.o_W8_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_st0O_S_le_st1O)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      k_i := k_i
      k_o := k_o
      k_s := k_s
      stk_i := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by exact hz.o_st0O_S_le_L))
      stk_o := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₃.kr (Nat.le_refl _) (part_sub (by exact hz.o_st1O_S_le_L))
      stk_k := k_stk
      stk_s := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₃.kr (Nat.le_refl _) low_sub
      scnw := by show (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀))
    (hk : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) opad) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine hinit_call hH hI hIsp hId ia fun s₄ rd₄ wr₄ cs₄ f₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz rd₄ wr₄ cs₄ (Nat.le_refl _) f₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_st0O_S_le_L⟩
      · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_st1O, by exact hz.o_st1O_S_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-- The inner state copied, and `update`'s arguments: the salt. -/
theorem su3_ok (hH : HashOK H) {s₄ : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s₄)
    (ri₄ : hH.SH.Repr s₄.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad))
    (ro₄ : hH.SH.Repr s₄.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) opad)) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.st0O .r15 H.stSO H.S)
      (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stSO ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)),
        .mov .rdx (.reg .r12), .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)))) s₄ fun t =>
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (sl s₀) ∧
      t.gpr .rsi = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide) (by decide)
    (so := H.st0O) (d := H.stSO) (n := H.S) (by exact hz.o_0_lt_S) (by exact hz.o_S_lt_p31) (s := s₄)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_st0O_S_le_L])))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_st0O_S_le_stSO)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_stSO_S_le_L))) fun s₅ c₅ => ?_)
  rw [h.kr.r15] at c₅
  have f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [c₅.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have k₅ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s₅ := ⟨h.kr.write hz c₅.rd c₅.wr (c₅.other _ (by decide) (by decide))
      (c₅.other _ (by decide) (by decide)) (o := H.stSO) (n := H.S) (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_L) f₅,
    by rw [c₅.other _ (by decide) (by decide), h.rbx], by rw [c₅.other _ (by decide) (by decide), h.rbp],
    by rw [c₅.other _ (by decide) (by decide), h.r12], by rw [c₅.other _ (by decide) (by decide), h.r13]⟩
  have dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_S_le_L)
  have ri₅ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH f₅ (dS _ (by exact hz.o_st0O_S_le_stSO)) ri₄
  have ro₅ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH f₅ (dS _ (by exact hz.o_st1O_S_le_stSO)) ro₄
  have rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad) := by rw [c₅.mem]; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_copy hH ri₄
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok k₅.kr.r15 (by exact hz.o_stSO_lt_p31) fun s₆ u₆ => wp_mov32i fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ =>
    wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ => WP.block_nil ?_
  have k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  have m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      zx_ofNat (by exact hz.o_B_lt_p32)], m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  exact
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r12]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.r13]
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
          u₆.other _ (by decide), k₅.kr.r15]
      cd := VG.Proof.Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp k₁₀.kr (by exact hz.o_stSO_hsS_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp k₁₀.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stSO) (by exact hz.o_stSO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := hp.sa_s.sub_right (part_sub (by exact hz.o_stSO_hsS_le_L))
      d_sc := hp.sa_s.sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L))
      stk_st := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₁₀.kr (by decide) (part_sub (by exact hz.o_stSO_hsS_le_L))
      stk_d := hp.stk_sa.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sub k₁₀.kr (by decide))
      stk_sc := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp k₁₀.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s₁₀)
    (ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (sl s₀))
    (hsi : s₁₀.gpr .rsi = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ t.mem := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hsnw := hp.snw
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream ua (by have := hp.sanw; omega) fun s₁₁ a₁₁ r₁₁ => ?_
  have k₁₁ := k₁₀.call hp hz a₁₁.rd a₁₁.wr a₁₁.cs (by decide) a₁₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stSO, by exact hz.o_stSO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  have dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region), ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, hH.stream.Wb⟩] ++
      [below (s₁₀.gpr .rsp) 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho =>
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.disj_call hp k₁₀.kr (part_sub (by omega_using [ho, hz.o_stSO_S_le_L])) (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_hsS_le_L)
      · exact (low_disj hz (by omega_using [ho₀, hz.o_W8_le_st0O]) (by omega_using [ho, hz.o_stSO_S_le_L])).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
  refine ⟨k₁₁, VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st0O) (by exact hz.o_st0O_S_le_stSO)) ri,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_stSO)) ro, ?_⟩
  have := r₁₁ _ rs (by rw [hsi, xorPad_length, VG.Proof.Pbkdf2.Md.X86_64.Pbk.blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hIsp : NoSp H.hmacInit) (hId : H.hmacInit.depth ≤ 2) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s)
    (hdx : s.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (hcx : (s.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀) (hk : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀)) :
    WP isa H.setup s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.su1_ok hp hz hH h hdx hcx hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.su2_ok hp hz hH hI hIsp hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, si₃, i₃, o₃, r₃⟩ => ?_))
  exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.su4_ok hp hz hH k₃ a₃ si₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkLoop`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s loop

After `k` blocks of the output (`Inv`), `out` holds the first `min (k D)
out_len` bytes of `T₁ ‖ … ‖ T_k`; a step computes `T_{k+1}` (`U₁` by `update`
with `INT (k + 1)` and HMAC's `finalize`, then `iterate`) and copies as much
of it as the output still needs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK ea_nat wp_mov32r zx32 contains_pre)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne InRegions.right' sub_of_off sub_of_self bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The specification's pieces -/

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hH : HashOK H) (s₀ : State) : List Byte → List Byte := hmacBlockKey hH.SH.H (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀)

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem (salt s₀) (sl s₀)

/-- `T_i`. -/
abbrev Tb (hH : HashOK H) (s₀ : State) (i : Nat) : List Byte := Spec.Pbkdf2.F (VG.Proof.Pbkdf2.Md.X86_64.Pbk.prf hH s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀) (cc s₀) i

/-- `T₁ ‖ … ‖ T_k`. -/
def G (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte := (List.range k).flatMap fun j => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Tb hH s₀ (j + 1)

theorem G_succ (hH : HashOK H) (s₀ : State) (k : Nat) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ (k + 1) = VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ k ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Tb hH s₀ (k + 1) := by
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Pbk.G, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The number of blocks of the output. -/
abbrev nb (H : Hash) (s₀ : State) : Nat := (ol s₀ + H.D - 1) / H.D

/-- The bytes of the output after `k` blocks. -/
abbrev done (H : Hash) (s₀ : State) (k : Nat) : Nat := min (k * H.D) (ol s₀)

theorem lt_nb {s₀ : State} (hD : 0 < H.D) {k : Nat} : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ ↔ k * H.D < ol s₀ := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega

theorem ol_le {s₀ : State} (hD : 0 < H.D) : ol s₀ ≤ VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ * H.D := by
  have h1 : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ * H.D + (ol s₀ + H.D - 1) % H.D = ol s₀ + H.D - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have h2 := Nat.mod_lt (ol s₀ + H.D - 1) hD
  omega

theorem nb_lt {s₀ : State} (hD : 0 < H.D) (h : ol s₀ ≤ (2 ^ 32 - 1) * H.D) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]; omega

theorem nb_zero {s₀ : State} (hD : 0 < H.D) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ = 0 ↔ ol s₀ = 0 := by
  have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb (s₀ := s₀) hD (k := 0); simp only [Nat.zero_mul] at this; omega

/-- After `k` blocks of the output. -/
structure Inv (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s
  st : VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ s.mem
  rbx : s.gpr .rbx = BitVec.ofNat 64 (k + 1)
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = BitVec.ofNat 64 (ol s₀ - VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ k)
  r13 : s.gpr .r13 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ + BitVec.ofNat 64 (VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ k)
  glen : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ k).length = k * H.D
  outB : bytesAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ k) = (VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ k).take (VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ k)

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem loopRegs_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) (h13 : s.gpr .r13 = s₀.gpr .rcx)
    (hS : VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ s.mem) :
    WP isa (.block H.loopRegs) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  unfold Hash.loopRegs
  refine wp_mov fun s₁ u₁ _ _ => ?_
  refine wp_movm (a := A s₀ H.outO) (by rw [ea_nat, u₁.other _ (by decide), h.r15])
    (by rw [u₁.rd, u₁.wr]; exact InRegions.right' (in_sc hp hz h.wr (by
      have := layout (H := H); have := end_le hz; exact hz.o_outO_8_le_L))) fun s₂ u₂ => ?_
  refine wp_movm (a := s₀.gpr .rsp + BitVec.ofNat 64 8)
    (by rw [ea_nat, u₂.other _ (by decide), u₁.other _ (by decide), h.rsp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, hp.rd]
        exact ⟨argR s₀, by simp, contains_pre (by decide)⟩) fun s₃ u₃ => ?_
  refine wp_mov32i fun s₄ u₄ _ _ => wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r12 : s₅.gpr .r12 = BitVec.ofNat 64 (ol s₀) := by
    rw [g₅, u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.olW hp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have k₅ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨⟨k₅.same rd₅ wr₅ (by rw [g₅]) (by rw [g₅]) m₅, ?_, ?_, ?_, ?_, ?_,
    by simp [VG.Proof.Pbkdf2.Md.X86_64.Pbk.G], by simp [bytesAt]⟩, ?_⟩
  · rw [m₅, m₄]; exact hS
  · rw [g₅, u₄.gpr]; rfl
  · rw [g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h13]
  · rw [r12]; simp
  · rw [g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, h.outW]; simp
  · rw [z₅, BitVec.and_self, ← g₅, r12, ofNat_beq_zero (stackArg s₀ 0).isLt]

end

/-! ## Facts about words and lengths -/

theorem bytes32_int (i : Nat) : VG.Proof.MdStream.bytes32 true (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [VG.Proof.MdStream.bytes32, ite_true, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;> omega

theorem sw32 (y : BitVec 32) : (y.setWidth 64).setWidth 32 = y := by
  have := y.isLt
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega

/-- Two disjoint regions that do not wrap around fit in the address space
together. -/
theorem len_add_le {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) (h₁ : r₁.base.toNat + r₁.len ≤ 2 ^ 64)
    (h₂ : r₂.base.toNat + r₂.len ≤ 2 ^ 64) : r₁.len + r₂.len ≤ 2 ^ 64 := by
  by_contra hc
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with hb | hb
  · refine hd r₂.base ?_ ?_ <;> simp only [Region.Contains]
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine hd r₁.base ?_ ?_ <;> simp only [Region.Contains]
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega

/-! ## A step, before `T` is copied out -/

/-- The registers a step keeps until `T` is copied out. -/
abbrev mregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem mregs_saved : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs, r ∈ calleeSaved := by decide

/-- In step `k`, before `T_{k+1}` is copied out: the key's states, the
registers, and the first `k` blocks in `out`. -/
structure Mid (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s
  st : VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ s.mem
  rbx : s.gpr .rbx = BitVec.ofNat 64 (k + 1)
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r12 : s.gpr .r12 = BitVec.ofNat 64 (ol s₀ - k * H.D)
  r13 : s.gpr .r13 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D)
  outB : bytesAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀) (k * H.D) = VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ k

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- What a call (or a write) leaves, writing parts of `scratch` from the
working state on, or its working space, and the stack below `rsp`. -/
theorem Mid.call (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs, s'.gpr r = s.gpr r)
    {ws : List Region} {n : Nat} (hn : n ≤ 24) (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ j, r = ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      ∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s' := by
  have hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  have ho : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀, k * H.D⟩ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀) := Region.sub_prefix hk
  have key : ∀ {X : Region}, (∀ o j, H.stWO ≤ o → o + j ≤ (H.W + H.S) * 8 → X.Disjoint (sR s₀ o j)) →
      X.Disjoint (lowR (H := H) s₀) → X.Disjoint (below (s.gpr .rsp) n) →
      ∀ r ∈ ws ++ [below (s.gpr .rsp) n], X.Disjoint r := by
    intro X h1 h2 h3 r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, ho1, ho2⟩
      · exact h2.sub_right (Region.sub_prefix hj)
      · exact h1 o j ho1 ho2
    · simp only [List.mem_singleton] at hr; subst hr; exact h3
  have hstk : ∀ {X : Region}, Region.Sub X (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀) → X.Disjoint (below (s.gpr .rsp) n) :=
    fun hX => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp h.kr hn hX).symm
  refine ⟨h.kr.keep hrd hwr (hcs _ (by simp)) (hcs _ (by simp)) hf
      (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_sv_64_le_stWO])) (by exact hz.o_sv_64_le_L) h2) (low_disj hz (by exact hz.o_W8_le_sv) (by exact hz.o_sv_64_le_L))
        (hstk (part_sub (by exact hz.o_sv_64_le_L)))) (fun r hr => ?_),
    h.st.keep hz hH hf (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_st0O_3mS_le_stWO])) (by exact hz.o_st0O_3mS_le_L) h2)
      (low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_3mS_le_L)) (hstk (part_sub (by exact hz.o_st0O_3mS_le_L)))),
    by rw [hcs _ (by simp), h.rbx], by rw [hcs _ (by simp), h.rbp],
    by rw [hcs _ (by simp), h.r12], by rw [hcs _ (by simp), h.r13], ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, _, h2⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, by simp, Region.sub_prefix (by show j ≤ (H.W + H.S) * 8; omega)⟩
      · exact ⟨_, by simp, part_sub h2⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sub h.kr hn⟩
  · rw [← h.outB]
    exact bytes_keep hf (key (fun o j _ h2 => (hp.o_s.sub_left ho).sub_right (part_sub h2))
      ((hp.o_s.sub_left ho).sub_right low_sub) ((hp.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sub h.kr hn)).sub_right ho).symm)
      (by have := hp.onw; omega)

/-- A write into a part of `scratch` from the working state on. -/
theorem Mid.write (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs, s'.gpr r = s.gpr r) {o n : Nat}
    (ho : H.stWO ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s' :=
  h.call hp hz hH hk hrd hwr hg (n := 0) (Nat.zero_le _) (hf.mono fun _ hr => List.mem_append_left _ hr)
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨o, n, rfl, ho, hon⟩

omit hp hz in
theorem Mid.upd {hH : HashOK H} {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s' := by
  have ne : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u ⟨(ne _ (by simp)).symm, (ne _ (by simp)).symm⟩, u.mem ▸ h.st,
    by rw [u.other _ (ne _ (by simp)), h.rbx], by rw [u.other _ (ne _ (by simp)), h.rbp],
    by rw [u.other _ (ne _ (by simp)), h.r12], by rw [u.other _ (ne _ (by simp)), h.r13],
    by rw [u.mem, h.outB]⟩

end

/-! ## Copying `T` out -/

theorem ea_r13 (s : State) (k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea { base := .r13, index := some .r14 } = s.gpr .r13 + BitVec.ofNat 64 k := by
  simp only [State.ea, h14]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, BitVec.add_zero]

theorem outLoop_ok {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State} (hc : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 H.tO + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr .r13 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .r15 + BitVec.ofNat 64 H.tO, n⟩ ⟨s.gpr .r13, n⟩) :
    WP isa H.outLoop s fun t => VG.Proof.Pbkdf2.Md.X86_64.Calls.Copied s (s.gpr .r13)
      (bytesAt s.mem (s.gpr .r15 + BitVec.ofNat 64 H.tO) n) t := by
  generalize eA : s.gpr .r15 + BitVec.ofNat 64 H.tO = A at hin hsep ⊢
  generalize eB : s.gpr .r13 = B at hout hsep ⊢
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Md.X86_64.Calls.CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop hn _ (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide), eA])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.ea_r13 _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), eB]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmp fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 (k + 1) := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14, VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ]
  have hcx : t₃.gpr .rcx = BitVec.ofNat 64 n := by
    rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.other _ (by decide) (by decide), hc]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14], ?_⟩, by rw [z₄, h14, hcx, sub_beq (by omega) (by omega)]⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, VG.Proof.Hmac.Generic.Common.bytesAt_snoc']
  have e : VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [VG.WriteBytes.writeBytes, hl, VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hsep hk (Nat.le_of_lt hk)
      (by omega), ↓reduceIte]
  have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k)
    (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega)
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']

/-! ## A step: `U₁` -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- `U₁ = PRF (S ‖ INT (k + 1))`. -/
abbrev U1 (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte :=
  hmacBlockKey hH.SH.H (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- Before `update` with `INT (k + 1)`. -/
structure AtUpd (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s
  args : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s (A s₀ H.stWO) (A s₀ H.intO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) 4
  rsi : s.gpr .rsi = s₀.gpr .rcx + (BitVec.ofNat 32 H.P.B).signExtend 64
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀)
  int : bytesAt s.mem (A s₀ H.intO) 4 = Spec.Pbkdf2.int (k + 1)

/-- Before HMAC's `finalize`. -/
structure AtFin (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s
  args : FinArgs (H := H) s (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .rcx + (BitVec.ofNat 32 (H.P.B + 4)).signExtend 64)
    (A s₀ H.uO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

/-- Before `iterate`. -/
structure AtIter (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s
  args : IterArgs (H := H) s (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀)
  u : bytesAt s.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.U1 hH s₀ k
  t : bytesAt s.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.U1 hH s₀ k

/-- A copy of the salted inner state, `INT (k + 1)`, and `update`'s arguments. -/
theorem pieceA_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.stSO .r15 H.stWO H.S) (.block H.intArgs)) s
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.AtUpd hH s₀ k) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  -- The working state, copied.
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide)
    (by decide) (so := H.stSO) (d := H.stWO) (n := H.S) (by exact hz.o_0_lt_S) (by exact hz.o_S_lt_p31) (s := s)
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L])))
    (fun j hj => by rw [h.kr.r15, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stWO_S_le_L]))
    (by rw [h.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_stSO_S_le_stWO)) (by exact hz.o_stSO_S_le_L) (by exact hz.o_stWO_S_le_L))) fun s₁ c₁ => ?_)
  rw [h.kr.r15] at c₁
  have m₁ := h.write hp hz hH (Nat.le_of_lt hkD) c₁.rd c₁.wr (fun r hr => c₁.other r (by rintro rfl; simp at hr)
    (by rintro rfl; simp at hr)) (o := H.stWO) (n := H.S) (Nat.le_refl _) (by exact hz.o_stWO_S_le_L) (by
      rw [c₁.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _))
  have rs₁ : hH.SH.Repr s₁.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀) := by
    rw [c₁.mem]; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_copy hH h.st.s
  -- `INT (k + 1)`.
  simp only [Hash.intArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov32r fun s₂ u₂ => wp_bswap32 fun s₃ u₃ => ?_
  have m₃ := (m₁.upd u₂ (by decide)).upd u₃ (by decide)
  refine wp_store32 (a := A s₀ H.intO) (by rw [ea_nat, m₃.kr.r15]) (in_sc hp hz m₃.kr.wr (by exact hz.o_intO_4_le_L))
    fun s₄ g₄ e₄ rd₄ wr₄ => ?_
  have f₄ : Frame [sR s₀ H.intO 4] s₃.mem s₄.mem := by
    rw [e₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have m₄ := m₃.write hp hz hH (Nat.le_of_lt hkD) rd₄ wr₄ (fun r _ => by rw [g₄]) (o := H.intO) (n := 4) (by exact hz.o_stWO_le_intO)
    (by exact hz.o_intO_4_le_L) f₄
  have e₄' : s₄.mem = VG.WriteBytes.writeBytes s₃.mem (A s₀ H.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [e₄, u₃.gpr, u₂.gpr, m₁.rbx, VG.Proof.Pbkdf2.Md.X86_64.Pbk.sw32, VG.Proof.Pbkdf2.Md.X86_64.Pbk.sw32,
      show (BitVec.ofNat 64 (k + 1)).setWidth 32 = BitVec.ofNat 32 (k + 1) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega),
      show bswap32 (BitVec.ofNat 32 (k + 1)) = if true then bswap32 (BitVec.ofNat 32 (k + 1)) else _ from rfl,
      writeW32, VG.Proof.Pbkdf2.Md.X86_64.Pbk.bytes32_int]
  -- `update`'s arguments.
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok m₄.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => ?_
  have m₇ := ((m₄.upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok m₇.kr.r15 (by exact hz.o_intO_lt_p31) fun s₈ u₈ => wp_mov32i fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ =>
    WP.block_nil ?_
  have m₁₀ := ((m₇.upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀ (by decide)
  have e₁₀ : s₁₀.mem = s₄.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have ua : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH.stream s₁₀ (A s₀ H.stWO) (A s₀ H.intO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) 4 :=
    { rdi := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
      rdx := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
      rcx := by rw [u₁₀.other _ (by decide), u₉.gpr]; rfl
      r8 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), m₇.kr.r15]
      cd := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₁₀.kr (o := H.intO) (n := 4) (by exact hz.o_intO_4_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₁₀.kr (by exact hz.o_stWO_hsS_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp m₁₀.kr (by rw [hWb]; exact hz.o_so_48_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      d_st := part_disj hz (Or.inr (by exact hz.o_stWO_hsS_le_intO)) (by exact hz.o_intO_4_le_L) (by exact hz.o_stWO_hsS_le_L)
      d_sc := (low_disj hz (by exact hz.o_W8_le_intO) (by exact hz.o_intO_4_le_L)).sub_right (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_W8))
      stk_st := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₁₀.kr (by decide) (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₁₀.kr (by decide) (part_sub (by exact hz.o_intO_4_le_L))
      stk_sc := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₁₀.kr (by decide) (Region.sub_prefix (by rw [hWb]; exact hz.o_so_48_le_L)) }
  refine ⟨m₁₀, ua, ?_, by rw [e₁₀]; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.repr_keep hH f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by exact hz.o_stWO_S_le_intO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_intO_4_le_L)) (by rw [u₃.mem, u₂.mem]; exact rs₁),
    by rw [e₁₀, e₄', VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (by rfl) (by decide)]⟩
  rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr,
    u₅.other _ (by decide), m₄.rbp]

/-- `update` with `INT (k + 1)`. -/
theorem callA_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.AtUpd hH s₀ k s) :
    WP isa (.call H.updN H.updC) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_call hH.stream h.args (by decide) fun s₁₁ a₁₁ r₁₁ => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁₁.rd a₁₁.wr (fun r hr => a₁₁.cs r (VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs_saved r hr)) (by decide)
      a₁₁.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_hsS_le_L⟩
        · exact .inl ⟨_, rfl, by rw [hWb]; exact hz.o_so_48_le_W8⟩
  · have := r₁₁ _ h.repr (by
      rw [h.rsi, sx_ofNat (by exact hz.o_B_lt_p31), List.length_append, xorPad_length,
        VG.Proof.Pbkdf2.Md.X86_64.Pbk.blockKey_length, bytesAt_length, Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    rwa [h.int] at this

/-- HMAC's `finalize`'s arguments. -/
theorem finArgs_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.block H.finArgs) s (VG.Proof.Pbkdf2.Md.X86_64.Pbk.AtFin hH s₀ k) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  -- `finalize`'s arguments.
  simp only [Hash.finArgs, List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok h.kr.r15 (by exact hz.o_stWO_lt_p31) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok ((u₁.other _ (by decide)).trans h.kr.r15) (by exact hz.o_st1O_lt_p31) fun s₂ u₂ => ?_
  simp only [List.cons_append]
  refine wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => ?_
  have m₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok m₄.kr.r15 (by exact hz.o_uO_lt_p31) fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have m₆ := (m₄.upd u₅ (by decide)).upd u₆ (by decide)
  have e₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stk : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below (s₆.gpr .rsp) 24).Disjoint (sR s₀ o n) :=
    fun h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₆.kr (Nat.le_refl _) (part_sub h)
  have fa : FinArgs (H := H) s₆ (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .rcx + (BitVec.ofNat 32 (H.P.B + 4)).signExtend 64)
      (A s₀ H.uO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) :=
    { rdi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      rsi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr]
      rdx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.rbp]
      rcx := by rw [u₆.other _ (by decide), u₅.gpr]
      r8 := by rw [u₆.gpr, u₅.other _ (by decide), m₄.kr.r15]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₆.kr (o := H.st1O) (n := H.S) (by exact hz.o_st1O_S_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₆.kr (by exact hz.o_stWO_S_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₆.kr (by exact hz.o_uO_D_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp m₆.kr (by exact hz.o_W8_le_L)
      i_u := part_disj hz (Or.inr (by exact hz.o_st1O_S_le_stWO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_stWO_S_le_uO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_uO_D_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_S_le_L)
      u_o := part_disj hz (Or.inl (by exact hz.o_st1O_S_le_uO)) (by exact hz.o_st1O_S_le_L) (by exact hz.o_uO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      stk_i := stk (by exact hz.o_stWO_S_le_L)
      stk_u := stk (by exact hz.o_st1O_S_le_L)
      stk_o := stk (by exact hz.o_uO_D_le_L)
      stk_s := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₆.kr (Nat.le_refl _) low_sub
      scnw := by have := hp.snw; omega }
  exact ⟨m₆, fa, by rw [e₆]; exact hr⟩

/-- HMAC's `finalize`: `U₁`. -/
theorem callB_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State}
    (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.AtFin hH s₀ k s) :
    WP isa (.call H.hmacFinN H.hmacFin) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.U1 hH s₀ k := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  refine hfin_call hH hF hFsp hFd h.args fun s₇ rd₇ wr₇ cs₇ f₇ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' rd₇ wr₇ (fun r hr => cs₇ r (VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs_saved r hr)) (Nat.le_refl _) f₇
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_S_le_L⟩
        · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_uO, by exact hz.o_uO_D_le_L⟩
        · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · have hK := VG.Proof.Pbkdf2.Md.X86_64.Pbk.blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    exact hpost _ _ hK (by rw [hK, List.length_append, bytesAt_length]; simp [Spec.Pbkdf2.int]; have := hz.o_B_5_le_L; omega)
      (by rw [← List.append_assoc]; exact h.repr)
      (by
        rw [sx_ofNat (by exact hz.o_B_4_lt_p31), List.length_append, bytesAt_length,
          show (Spec.Pbkdf2.int (k + 1)).length = 4 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have : sl s₀ = (s₀.gpr .rcx).toNat := rfl
        omega)
      h.mid.st.o

/-- `U` copied to `T`, and `iterate`'s arguments. -/
theorem pieceC_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s₇ : State} (m₇ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s₇)
    (hU : bytesAt s₇.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.U1 hH s₀ k) :
    WP isa (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.uO .r15 H.tO H.D) (.block H.iterArgs)) s₇
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.AtIter hH s₀ k) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  -- `U` copied to `T`.
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.copy_ok (src := .r15) (dst := .r15) (by decide)
    (by decide) (so := H.uO) (d := H.tO) (n := H.D) hD.1 (by exact hz.o_D_lt_p31) (s := s₇)
    (fun j hj => by rw [m₇.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz m₇.kr.wr (by omega_using [hj, hz.o_uO_D_le_L])))
    (fun j hj => by rw [m₇.kr.r15, add_ofNat]; exact in_sc hp hz m₇.kr.wr (by omega_using [hj, hz.o_tO_D_le_L]))
    (by rw [m₇.kr.r15]; exact part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L))) fun s₈ c₈ => ?_)
  rw [m₇.kr.r15] at c₈
  have f₈ : Frame [sR s₀ H.tO H.D] s₇.mem s₈.mem := by
    rw [c₈.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have m₈ := m₇.write hp hz hH hk' c₈.rd c₈.wr (fun r hr => c₈.other r (by rintro rfl; simp at hr)
    (by rintro rfl; simp at hr)) (o := H.tO) (n := H.D) (by exact hz.o_stWO_le_tO) (by exact hz.o_tO_D_le_L) f₈
  have hU₈ : bytesAt s₈.mem (A s₀ H.uO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D :=
    bytes_keep f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)) (by exact hz.o_D_le_p64)
  have hT₈ : bytesAt s₈.mem (A s₀ H.tO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D := by
    rw [c₈.mem]; exact VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by exact hz.o_D_lt_p64)
  -- `iterate`'s arguments.
  simp only [Hash.iterArgs, List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok m₈.kr.r15 (by exact hz.o_st0O_lt_p31) fun s₉ u₉ => ?_
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok ((u₉.other _ (by decide)).trans m₈.kr.r15) (by exact hz.o_uO_lt_p31) fun s₁₀ u₁₀ => ?_
  have m₁₀ := (m₈.upd u₉ (by decide)).upd u₁₀ (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_movm (a := A s₀ H.cO) (by rw [ea_nat, m₁₀.kr.r15])
    (InRegions.right' (in_sc hp hz m₁₀.kr.wr (by exact hz.o_cO_8_le_L))) fun s₁₁ u₁₁ => ?_
  have m₁₁ := m₁₀.upd u₁₁ (by decide)
  refine VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_ok m₁₁.kr.r15 (by exact hz.o_tO_lt_p31) fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ _ _ => WP.block_nil ?_
  have m₁₃ := (m₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  have e₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have stk' : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below (s₁₃.gpr .rsp) 24).Disjoint (sR s₀ o n) :=
    fun h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₁₃.kr (Nat.le_refl _) (part_sub h)
  have ia : IterArgs (H := H) s₁₃ (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) :=
    { rdi := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.gpr]
      rsi := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr]
      rdx := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.kr.cW]
      rcx := by rw [u₁₃.other _ (by decide), u₁₂.gpr]
      r8 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), m₁₁.kr.r15]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', h', off, e, l⟩ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₁₃.kr (o := H.st0O) (n := 2 * H.S) (by exact hz.o_st0O_2mS_le_L)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
        · obtain ⟨r', h', off, e, l⟩ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₁₃.kr (o := H.uO) (n := H.D) (by exact hz.o_uO_D_le_L)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp m₁₃.kr (by exact hz.o_tO_D_le_L)
        · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_low hp m₁₃.kr (by exact hz.o_W8_le_L)
      k_t := part_disj hz (Or.inl (by exact hz.o_st0O_2mS_le_tO)) (by exact hz.o_st0O_2mS_le_L) (by exact hz.o_tO_D_le_L)
      k_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_2mS_le_L)
      u_t := part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      t_s := low_disj hz (by exact hz.o_W8_le_tO) (by exact hz.o_tO_D_le_L)
      stk_k := stk' (by exact hz.o_st0O_2mS_le_L)
      stk_u := stk' (by exact hz.o_uO_D_le_L)
      stk_t := stk' (by exact hz.o_tO_D_le_L)
      stk_s := VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp m₁₃.kr (Nat.le_refl _) low_sub
      knw := by
        have := hp.snw
        simp only [A, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := hz.o_st0O_2mS_le_L; have := L_lt hz; omega
      scnw := by have := hp.snw; omega }
  exact ⟨m₁₃, ia, by rw [e₁₃, hU₈, hU], by rw [e₁₃, hT₈, hU]⟩

/-- `iterate`: `T_{k+1}`. -/
theorem callC_ok (hH : HashOK H) (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate)
    (hId : H.iterate.depth ≤ 2) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.AtIter hH s₀ k s) :
    WP isa (.call H.iterN H.iterate) s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.Tb hH s₀ (k + 1) := by
  have hW := hz.W
  have hD := hz.z.D
  have hWb : hH.stream.Wb = H.P.so + 48 := rfl
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  refine iter_call hH hI hIsp hId h.args fun s₁₄ rd₁₄ wr₁₄ cs₁₄ f₁₄ hpost' => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' rd₁₄ wr₁₄ (fun r hr => cs₁₄ r (VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs_saved r hr)) (Nat.le_refl _) f₁₄
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_tO, by exact hz.o_tO_D_le_L⟩
        · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  have hK := VG.Proof.Pbkdf2.Md.X86_64.Pbk.blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have hc : ((BitVec.ofNat 64 (cc s₀ - 1)).setWidth 32).toNat = cc s₀ - 1 := by
    have := ((s₀.gpr .r8).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hO : A s₀ H.st0O + BitVec.ofNat 64 H.S = A s₀ H.st1O := by
    rw [add_ofNat, show H.st0O + H.S = H.st1O by exact hz.o_st0O_S_eq_st1O]
  rw [hpost' _ hK h.mid.st.i (hO ▸ h.mid.st.o), hc, h.u, h.t]
  rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem Mid.same {hH : HashOK H} {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s' :=
  ⟨h.kr.same hrd hwr (by rw [hg]) (by rw [hg]) hm, hm ▸ h.st, by rw [hg, h.rbx], by rw [hg, h.rbp],
    by rw [hg, h.r12], by rw [hg, h.r13], by rw [hm, h.outB]⟩

omit hp in
/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {hH : HashOK H} {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) :
    WP isa H.outLen s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧ t.gpr .rcx = BitVec.ofNat 64 (min (ol s₀ - k * H.D) H.D) ∧
      t.mem = s.mem := by
  have hD := hz.z.D; have hN := hz.z.N
  have hol : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  unfold Hash.outLen
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_cmp fun s₂ g₂ m₂ rd₂ wr₂ c₂ _ => WP.block_nil ?_)
  have e₂ : s₂.mem = s.mem := by rw [m₂, u₁.mem]
  have m₂ := (h.upd u₁ (by decide)).same rd₂ wr₂ g₂ m₂
  have rcx : s₂.gpr .rcx = BitVec.ofNat 64 H.D := by rw [g₂, u₁.gpr, zx_ofNat (by exact hz.o_D_lt_p32)]
  have cf : s₂.cf = some (decide (ol s₀ - k * H.D < H.D)) := by
    rw [c₂, ← g₂, m₂.r12, rcx, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by exact hz.o_D_lt_p64)]
  refine WP.ite (decide (ol s₀ - k * H.D < H.D)) (by simp [eval, cf]) (fun hT => ?_) fun hF => WP.block_nil ?_
  · refine wp_mov fun s₃ u₃ _ _ => WP.block_nil ⟨m₂.upd u₃ (by decide), ?_, by rw [u₃.mem, e₂]⟩
    have : ol s₀ - k * H.D < H.D := of_decide_eq_true hT
    rw [u₃.gpr, m₂.r12, Nat.min_eq_left (Nat.le_of_lt this)]
  · have : ¬ ol s₀ - k * H.D < H.D := of_decide_eq_false (by simpa using hF)
    exact ⟨m₂, by rw [rcx, Nat.min_eq_right (by omega)], e₂⟩

/-- Copying as much of `T_{k+1}` as the output needs, and on to the next block. -/
theorem tail_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) (hg : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ k).length = k * H.D) {s : State}
    (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) (ht : bytesAt s.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.Tb hH s₀ (k + 1)) :
    WP isa (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) s fun t =>
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀)) := by
  have hL := L_lt hz
  have hD := hz.z.D; have hN := hz.z.N
  have hol : ol s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hD.1).1 hk
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_lt hD.1 hp.olD; omega
  have hk1 := VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb (s₀ := s₀) hD.1 (k := k + 1)
  rw [Nat.succ_mul] at hk1
  have hon := hp.onw
  generalize en : min (ol s₀ - k * H.D) H.D = n
  have hn : 0 < n ∧ n ≤ H.D ∧ k * H.D + n ≤ ol s₀ := by omega
  have hdn : VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ (k + 1) = k * H.D + n := by
    show min ((k + 1) * H.D) (ol s₀) = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀) := Offset.sub_base _ hn.2.2
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outLen_ok hz h) fun s₁ ⟨m₁, rc₁, e₁⟩ => ?_)
  rw [en] at rc₁
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outLoop_ok (n := n) hn.1 (by omega) rc₁
    (fun j hj => by rw [m₁.kr.r15, add_ofNat]; exact InRegions.right' (in_sc hp hz m₁.kr.wr (by omega_using [hj, hn.2.1, hz.o_tO_D_le_L])))
    (fun j hj => by
      rw [m₁.r13, add_ofNat]
      exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, by rw [m₁.kr.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [m₁.kr.r15, m₁.r13]; exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_using [hn.2.1, hz.o_tO_D_le_L]))).symm))
    fun s₂ c₂ => ?_)
  rw [m₁.kr.r15, m₁.r13] at c₂
  have f₂ : Frame [(⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)] s₁.mem s₂.mem := by
    rw [c₂.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have od : ∀ {X : Region}, Region.Sub X (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀) →
      ∀ r ∈ [(⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.o_s.sub_left osub).sub_right hX).symm
  have k₂ : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s₂ := m₁.kr.keep c₂.rd c₂.wr (c₂.other _ (by decide) (by decide))
    (c₂.other _ (by decide) (by decide)) f₂ (od (part_sub (by exact hz.o_sv_64_le_L))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  refine wp_add fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r13 → r ≠ .rbx → s₄.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, c₂.other r h1 h2]
  have e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₅]; exact m₁.st.keep hz hH f₂ (od (part_sub (by exact hz.o_st0O_3mS_le_L)))
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), c₂.other _ (by decide) (by decide), m₁.rbx,
      VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ]
  · rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), m₁.rbp]
  · rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide)
      (by decide), m₁.r12, rc₁, sub_ofNat (by omega), hdn]
    congr 1; omega
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, c₂.other _ (by decide) (by decide),
      c₂.other _ (by decide) (by decide), m₁.r13, rc₁, add_ofNat, hdn]
  · rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.G_succ, List.length_append, hg, ← ht, bytesAt_length, Nat.succ_mul]
  · rw [e₅, hdn, bytesAt_add, bytes_keep f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega)).symm)
      (by omega),
      c₂.mem, VG.Proof.Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega),
      m₁.outB, VG.Proof.Pbkdf2.Md.X86_64.Pbk.G_succ, ← hg, List.take_length_add_append, ← ht, e₁, ← bytesAt_take _ _ hn.2.1]
  · rw [z₅, g₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide)
      (by decide), m₁.r12, rc₁, sub_beq (by omega) (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega

/-! ## The loop and `pbkdf2` -/

/-- One block of the output. -/
theorem block_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ k s) :
    WP isa H.block s fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀)) := by
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hz.z.D.1).1 hk
  have hd : VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  have m : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s := ⟨h.kr, h.st, h.rbx, h.rbp, by rw [h.r12, hd], by rw [h.r13, hd], hb⟩
  unfold Hash.block
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pieceA_ok hp hz hH hk m) fun s₁ h₁ => ?_))
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.callA_ok hp hz hH hk h₁) fun s₂ ⟨m₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.finArgs_ok hp hz hH hk m₂ r₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.callB_ok hp hz hH hF hFsp hFd hk h₃) fun s₄ ⟨m₄, u₄⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pieceC_ok hp hz hH hk m₄ u₄) fun s₅ h₅ => ?_))
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.callC_ok hp hz hH hI hIsp hId hk h₅) fun s₆ ⟨m₆, t₆⟩ => ?_)
  exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.tail_ok hp hz hH hk h.glen m₆ t₆

/-- The loop over the blocks of the output: none when `out_len = 0`. -/
theorem loop_ok (hH : HashOK H) (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ 0 s) (hz0 : s.zf = some (decide (ol s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop H.block .ne)) s (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀)) := by
  have hD := hz.z.D.1
  refine WP.ite (decide (ol s₀ = 0)) (by simp [eval, hz0]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [(VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_zero hD).2 (of_decide_eq_true h0)]; exact h
  · have : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ ≠ 0 := fun e => by simp [(VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_zero hD).1 e] at h0
    exact VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop (Nat.pos_of_ne_zero this) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀)
      (fun k hk t ht => VG.Proof.Pbkdf2.Md.X86_64.Pbk.block_ok hp hz hH hF hFsp hFd hI hIsp hId hk ht) h

theorem correct (hH : HashOK H) (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W))
    (hInsp : NoSp H.hmacInit) (hInd : H.hmacInit.depth ≤ 2)
    (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W))
    (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2) :
    WP isa H.pbkdf2 s₀ fun s' => gprPreserved s₀ s' ∧ (pbkG hH.SH (H.W + H.S)).post s₀ s' := by
  have hD := hz.z.D.1; have hW := hz.W
  unfold Hash.pbkdf2
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.loadScr_ok hp) fun s₀' l => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_ok hp hz l) fun s₁ ⟨k₁, bx, bp, r12, r13, cf⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.key_ok hp hz hH ⟨k₁, bx, bp, r12, r13⟩ cf) fun s₂ ⟨k₂, dx₂, cx₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.setup_ok hp hz hH hIn hInsp hInd k₂ dx₂ cx₂ ka) fun s₃ ⟨k₃, st₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.loopRegs_ok hp hz hH k₃.kr k₃.r13 st₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.loop_ok hp hz hH hF hFsp hFd hI hIsp hId i₄ z₄) fun s₅ i₅ => ?_)
  have k₅ := i₅.kr
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.restore_ok H.hh k₅.r15 hW k₅.saved (VG.Proof.Pbkdf2.Md.X86_64.Pbk.in_wr hp k₅)
    (by have : H.S = H.P.N + H.P.B := rfl; have := hz.z.B; show 8 * H.W + 48 ≤ (H.W + H.S) * 8; exact hz.o_W8_48_le_L))
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₅.ret hp]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  have hdone : VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) = ol s₀ := by
    have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol_le (s₀ := s₀) hD; show min _ _ = _; omega
  have hb := i₅.outB
  rw [hdone] at hb
  show Spec.Pbkdf2.pbkdf2 (Spec.Hmac.hmac hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))) hH.SH.digestBytes
    (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀) (cc s₀) (ol s₀) = some (bytesAt s'.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀) (ol s₀))
  have hol := hp.olD
  rw [hH.hD, Spec.Pbkdf2.pbkdf2, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm, hb]
  rfl

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Pbkdf2CT`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`, constant time

The pieces between the calls are checked by the taint analysis (`Checks`, `by
taint_decide` for each hash function), each from registers that the
correctness proof fixes to public values (`KE`, `Mid`, `KR`): they are the
same in two runs that agree on the public arguments. The calls are constant
time by their callees' proofs (`RelCT.call`, with arguments the correctness
proof fixes to the same values), and the branches and the loop go the same way
in both runs, by the facts the correctness proof gives about their flags.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK pbkG pbkImp)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG rel_taint rel_wp)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-- The taint checks of the pieces of `pbkdf2` between its calls, branches
and loops. -/
structure Checks (H : Hash) : Prop where
  load : ∃ hc, (Taint.check taint (Taint.ofRegs [.rsp]) (.block Hash.loadScr) hc).isSome = true
  entry : ∃ hc, (Taint.check taint (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (.block H.entry) hc).isSome = true
  hk1 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO)) hc).isSome = true
  hk3 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) hc).isSome = true
  hk5 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) hc).isSome = true
  hk7 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) hc).isSome = true
  short : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.block [.mov .rdx (.reg .rbx), .mov .rcx (.reg .rbp)]) hc).isSome = true
  su1 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.st0O ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rsi H.st1O ++
      ([.mov .r8 (.reg .r15)] : List Instr))) hc).isSome = true
  su3 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
    (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.st0O .r15 H.stSO H.S)
      (.block (VG.Impl.Pbkdf2.Md.X86_64.scr .rdi H.stSO ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)),
        .mov .rdx (.reg .r12), .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)))) hc).isSome = true
  loopRegs : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.kregs) (.block H.loopRegs) hc).isSome = true
  pieceA : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs)
    (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.stSO .r15 H.stWO H.S) (.block H.intArgs)) hc).isSome = true
  finArgs : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs) (.block H.finArgs) hc).isSome = true
  pieceC : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs)
    (.seq (VG.Impl.Pbkdf2.Md.X86_64.copy .r15 H.uO .r15 H.tO H.D) (.block H.iterArgs)) hc).isSome = true
  tail : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs)
    (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) hc).isSome = true
  exit : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.kregs) (.block H.exit) hc).isSome = true

/-- The public arguments are the same (`c` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : (s₀.gpr .r8).setWidth 32 = (s₀'.gpr .r8).setWidth 32
  r9 : s₀.gpr .r9 = s₀'.gpr .r9
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PubEq s₀ s₀')
include hq

/-! ## What agrees in the two runs -/

theorem scr_eq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀' = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀ := hq.a1.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀' + _ = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀ + _; rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq]
theorem pw_eq : pw s₀' = pw s₀ := hq.rdi.symm
theorem pwl_eq : pwl s₀' = pwl s₀ := by show (s₀'.gpr .rsi).toNat = _; rw [← hq.rsi]
theorem salt_eq : salt s₀' = salt s₀ := hq.rdx.symm
theorem sl_eq : sl s₀' = sl s₀ := by show (s₀'.gpr .rcx).toNat = _; rw [← hq.rcx]
theorem cc_eq : cc s₀' = cc s₀ := by show ((s₀'.gpr .r8).setWidth 32).toNat = _; rw [← hq.r8]
theorem out_eq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀' = VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀ := hq.r9.symm
theorem ol_eq : ol s₀' = ol s₀ := by show (stackArg s₀' 0).toNat = _; rw [← hq.a0]
theorem nb_eq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀' = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ := by show (ol s₀' + H.D - 1) / H.D = _; rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol_eq hq]
theorem kp_eq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀' = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pw s₀' else A s₀' H.hkO) = _; rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq]
theorem kl_eq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀' = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pwl s₀' else H.D) = _; rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl_eq hq]

theorem kr_agree {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.r15, h'.r15, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq]
  · rw [h.rsp, h'.rsp, hq.rsp]

theorem ke_agree {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw_eq hq]
  · rw [h.rbp, h'.rbp, hq.rsi]
  · rw [h.r12, h'.r12, VG.Proof.Pbkdf2.Md.X86_64.Pbk.salt_eq hq]
  · rw [h.r13, h'.r13, hq.rcx]
  · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.kr_agree hq h.kr h'.kr _ (by simp)
  · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.kr_agree hq h.kr h'.kr _ (by simp)

theorem mid_agree {hH : HashOK H} {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]
  · rw [h.rbp, h'.rbp, hq.rcx]
  · rw [h.r12, h'.r12, VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol_eq hq]
  · rw [h.r13, h'.r13, VG.Proof.Pbkdf2.Md.X86_64.Pbk.out_eq hq]
  · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.kr_agree hq h.kr h'.kr _ (by simp)
  · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.kr_agree hq h.kr h'.kr _ (by simp)

theorem ke_rsp {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s') : s.gpr .rsp = s'.gpr .rsp :=
  VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_agree hq h h' _ (by simp)

end

/-! ## The pieces in two runs -/

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hp' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀') (hz : PSizes H)
  (hq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Checks H)
include hH hp hp' hz hq hc

omit hH in
/-- The entry, up to the comparison of the password's length. -/
theorem entry_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.seq (.block Hash.loadScr) (.block H.entry))
    fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1))) ∧
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ s'.cf = some (decide (pwl s₀' < H.P.B + 1))) := by
  have l := rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.Pbkdf2.Md.X86_64.Pbk.Loaded s₀) (G' := VG.Proof.Pbkdf2.Md.X86_64.Pbk.Loaded s₀') [.rsp]
    (fun s s' e e' r hr => by
      rw [e, e']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hq.rsp) hc.load
    (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.loadScr_ok hp) (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.loadScr_ok hp')
  have e := rel_taint (F := VG.Proof.Pbkdf2.Md.X86_64.Pbk.Loaded s₀) (F' := VG.Proof.Pbkdf2.Md.X86_64.Pbk.Loaded s₀')
    (G := fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1)))
    (G' := fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s ∧ s.cf = some (decide (pwl s₀' < H.P.B + 1)))
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun s s' l l' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rdi]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rsi]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rdx]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rcx]
      · rw [l.r8, l'.r8, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.r9]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rsp]) hc.entry
    (fun _ l => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_ok hp hz l) fun _ ⟨k, a, b, c, d, f⟩ => ⟨⟨k, a, b, c, d⟩, f⟩)
    (fun _ l => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_ok hp' hz l) fun _ ⟨k, a, b, c, d, f⟩ => ⟨⟨k, a, b, c, d⟩, f⟩)
  exact l.seq e

/-- Hashing a password longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s') => VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO)
    (G' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' t ∧ t.gpr .rdi = A s₀' H.stWO) VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs ag hc.hk1
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk1_ok hz h) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) σ₀ → VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.S⟩] s.wr ∧ (below (s.gpr .rsp) 16).Disjoint ⟨A σ₀ H.stWO, H.S⟩ :=
    fun hp h => ⟨Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.cov_part hp h.kr (by omega),
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk_sc hp h.kr (by omega) (part_sub (by omega))⟩
  have c₂ := rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.gpr .rdi = A s₀ H.stWO) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ s'.gpr .rdi = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i.1, i'.1, i.2, i'.2, VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_rsp hq h.1.1 h.2.1⟩)
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk2_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk3_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk5_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧ bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h) fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_rsp hq k k'⟩)
        (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.rsi], VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_rsp hq k k'⟩)
        (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1))) ∧
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ s'.cf = some (decide (pwl s₀' < H.P.B + 1)))) H.key
    fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ ∧ (s.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ ∧
        VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀)) ∧
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ s'.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀' ∧ (s'.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀' ∧
        VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀' s'.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀')) := by
  have ite : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1))) ∧
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ s'.cf = some (decide (pwl s₀' < H.P.B + 1)))) H.key fun _ _ => True := by
    unfold Hash.key
    refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl_eq hq]) ?_ ?_
    · exact (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · obtain ⟨_, hs⟩ := hc.short
      exact RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs)
        (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_agree hq h.1.1.1 h.1.2.1)) hs
  exact (ite.wp fun s s' h => ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.key_ok hp hz hH h.1.1 h.1.2, VG.Proof.Pbkdf2.Md.X86_64.Pbk.key_ok hp' hz hH h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- HMAC's states, and the inner one after the salt. -/
theorem setup_rel (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hInsp : NoSp H.hmacInit)
    (hInd : H.hmacInit.depth ≤ 2) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ ∧ (s.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ ∧
        VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀)) ∧
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ s'.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀' ∧ (s'.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀' ∧
        VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀' s'.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀'))) H.setup
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ s.mem) ∧ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s' ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀' s'.mem) := by
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s') => VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_agree hq h h'
  unfold Hash.setup
  have r₁ := rel_taint
    (F := fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ s.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀ ∧ (s.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀ ∧
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀))
    (F' := fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s ∧ s.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀' ∧ (s.gpr .rcx).toNat = VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀' ∧
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀' s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀'))
    (G := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀) ∧
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀))
    (G' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' t ∧
      InitArgs (H := H) t (A s₀' H.st0O) (A s₀' H.st1O) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀') ∧
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.KeyAt hH s₀' t.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl H s₀'))
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.su1
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su1_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su1_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  have r₃ := rel_taint (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) Spec.Hmac.opad))
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' t ∧
      hH.SH.Repr t.mem (A s₀' H.st0O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀') Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀' H.st1O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀') Spec.Hmac.opad)) VG.Proof.Pbkdf2.Md.X86_64.Pbk.eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.su3
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su3_ok hp hz hH h.1 h.2.1 h.2.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su3_ok hp' hz hH h.1 h.2.1 h.2.2)
  refine r₁.seq (RelCT.seq ?_ (RelCT.assoc (r₃.seq ?_)))
  · exact rel_wp (hinit_rel hH hIn fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.kp_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.kl_eq hq] at a'
        exact ⟨a, a', VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_rsp hq k k'⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su2_ok hp hz hH hIn hInsp hInd h.1 h.2.1 h.2.2)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su2_ok hp' hz hH hIn hInsp hInd h.1 h.2.1 h.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_rel hH.stream fun s s' h => by
        obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
        rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.salt_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.sl_eq hq] at a'
        exact ⟨a, a', by rw [i, i'], VG.Proof.Pbkdf2.Md.X86_64.Pbk.ke_rsp hq k k'⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.su4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)

end

/-! ## The blocks of the output -/

theorem inv_mid {hH : HashOK H} {s₀ : State} (hz : PSizes H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) {s : State}
    (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ k s) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s := by
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lt_nb hz.z.D.1).1 hk
  have hd : VG.Proof.Pbkdf2.Md.X86_64.Pbk.done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  exact ⟨h.kr, h.st, h.rbx, h.rbp, by rw [h.r12, hd], by rw [h.r13, hd], hb⟩

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LI (hH : HashOK H) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  n ≤ VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ ∧ 0 < n ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - n) s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - n) s'

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hp' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀') (hz : PSizes H)
  (hq : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Checks H)
  (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
  (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
include hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId

theorem block_mid_rel {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) (hg : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀ k).length = k * H.D)
    (hg' : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.G hH s₀' k).length = k * H.D) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k s') H.block fun _ _ => True := by
  have hk' : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀' := by rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_eq hq]; exact hk
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s) (h' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k s') => VG.Proof.Pbkdf2.Md.X86_64.Pbk.mid_agree hq h h'
  have msp : ∀ {s s' : State}, VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k s → VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k s' → s.gpr .rsp = s'.gpr .rsp :=
    fun h h' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.mid_agree hq h h' _ (by simp)
  unfold Hash.block
  have pA := rel_taint VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs ag hc.pieceA (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.pieceA_ok hp hz hH hk h) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.pieceA_ok hp' hz hH hk' h)
  have fA := rel_taint
    (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧ hH.SH.Repr t.mem (A s₀ H.stWO)
      (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀) Spec.Hmac.ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k t ∧ hH.SH.Repr t.mem (A s₀' H.stWO)
      (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.X86_64.Pbk.K0 hH s₀') Spec.Hmac.ipad ++ VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltB s₀' ++ Spec.Pbkdf2.int (k + 1)))
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs (fun s s' h h' => ag s s' h.1 h'.1) hc.finArgs
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.finArgs_ok hp hz hH hk h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.finArgs_ok hp' hz hH hk' h.1 h.2)
  have pC := rel_taint
    (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.U1 hH s₀ k)
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.uO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.U1 hH s₀' k)
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs (fun s s' h h' => ag s s' h.1 h'.1) hc.pieceC
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.pieceC_ok hp hz hH hk h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.pieceC_ok hp' hz hH hk' h.1 h.2)
  have tl := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.Tb hH s₀ (k + 1))
    (F' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.tO) H.D = VG.Proof.Pbkdf2.Md.X86_64.Pbk.Tb hH s₀' (k + 1))
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.mregs (fun s s' h h' => ag s s' h.1 h'.1) hc.tail
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.tail_ok hp hz hH hk hg h.1 h.2) fun _ _ => trivial)
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Pbk.tail_ok hp' hz hH hk' hg' h.1 h.2) fun _ _ => trivial)
  refine (RelCT.assoc (pA.seq (RelCT.seq ?_ (fA.seq (RelCT.seq ?_ (RelCT.assoc (pC.seq (RelCT.seq ?_ tl)))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.upd_rel hH.stream fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq] at x
        exact ⟨a.args, x, by rw [a.rsi, a'.rsi, hq.rcx], msp a.mid a'.mid⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.callA_ok hp hz hH hk h) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.callA_ok hp' hz hH hk' h)
  · exact rel_wp (hfin_rel hH hF fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, ← hq.rcx, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.callB_ok hp hz hH hF hFsp hFd hk h) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.callB_ok hp' hz hH hF hFsp hFd hk' h)
  · exact rel_wp (iter_rel hH hI fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.cc_eq hq, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.callC_ok hp hz hH hI hIsp hId hk h) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.callC_ok hp' hz hH hI hIsp hId hk' h)

theorem block_rel {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ k s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' k s') H.block fun s s' =>
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀))) ∧
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' (k + 1) s' ∧ s'.zf = some (decide (k + 1 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀'))) := by
  have hk' : k < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀' := by rw [VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_eq hq]; exact hk
  intro s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂
  refine ((((VG.Proof.Pbkdf2.Md.X86_64.Pbk.block_mid_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId hk h.1.glen h.2.glen).mono
    (P' := fun s s' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ k s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' k s') (fun _ _ h => ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.inv_mid hz hk h.1, VG.Proof.Pbkdf2.Md.X86_64.Pbk.inv_mid hz hk' h.2⟩)
    fun _ _ h => h).wp fun s s' h => ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.block_ok hp hz hH hF hFsp hFd hI hIsp hId hk h.1,
      VG.Proof.Pbkdf2.Md.X86_64.Pbk.block_ok hp' hz hH hF hFsp hFd hI hIsp hId hk' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2)
    _ _ _ _ _ _ h e₁ e₂

theorem step_rel (n : Nat) :
    RelCT isa (VG.Proof.Pbkdf2.Md.X86_64.Pbk.LI hH s₀ s₀' n) H.block fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀') s') ∧
      (isa.eval .ne s = some true → ∃ m < n, VG.Proof.Pbkdf2.Md.X86_64.Pbk.LI hH s₀ s₀' m s s') := by
  by_cases hn : n ≤ VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ ∧ 0 < n
  · have hk : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - n < VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ := by omega
    refine ((VG.Proof.Pbkdf2.Md.X86_64.Pbk.block_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId hk).mono (P' := VG.Proof.Pbkdf2.Md.X86_64.Pbk.LI hH s₀ s₀' n)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_eq (H := H) hq
    have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
    rw [ev, ev, z, z', e]
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - n + 1 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ := by simpa using hf
      rw [hl] at i i'
      exact ⟨i, i'⟩
    · have hl : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - n + 1 ≠ VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ := by simpa using ht
      have e' : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - (n - 1) = VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ - n + 1 := by omega
      exact ⟨n - 1, by omega, by omega, by omega, e' ▸ i, e' ▸ i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0))) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' 0 s' ∧ s'.zf = some (decide (ol s₀' = 0))))
      (.ite .e (.block []) (.loop H.block .ne)) fun s s' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀') s' := by
  have hD := hz.z.D.1
  have e := VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_eq (H := H) hq; have eo := VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol_eq hq
  refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, eo]) ?_ ?_
  · refine RelCT.block_nil fun s s' h => ?_
    have h0 : ol s₀ = 0 := by simpa [eval, h.1.1.2] using h.2
    rw [e, (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_zero hD).2 h0]
    exact ⟨h.1.1.1, h.1.2.1⟩
  · refine (RelCT.loop (M := isa) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.LI hH s₀ s₀') (VG.Proof.Pbkdf2.Md.X86_64.Pbk.step_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId)
      (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have h0 : ol s₀ ≠ 0 := by simpa [eval, h.1.1.2] using h.2
    have : VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀ ≠ 0 := fun x => h0 ((VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb_zero hD).1 x)
    refine ⟨Nat.le_refl _, Nat.pos_of_ne_zero this, ?_, ?_⟩ <;> rw [Nat.sub_self]
    exacts [h.1.1.1, h.1.2.1]

theorem ct (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hInsp : NoSp H.hmacInit)
    (hInd : H.hmacInit.depth ≤ 2) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.pbkdf2 fun _ _ => True := by
  unfold Hash.pbkdf2
  have lr := rel_taint (F := fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀ s.mem)
    (F' := fun s => VG.Proof.Pbkdf2.Md.X86_64.Pbk.KE (H := H) s₀' s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.States hH s₀' s.mem)
    (G := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)))
    (G' := fun t => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' 0 t ∧ t.zf = some (decide (ol s₀' = 0)))
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.kregs (fun s s' h h' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.kr_agree hq h.1.kr h'.1.kr) hc.loopRegs
    (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.loopRegs_ok hp hz hH h.1.kr h.1.r13 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.X86_64.Pbk.loopRegs_ok hp' hz hH h.1.kr h.1.r13 h.2)
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.X86_64.Pbk.nb H s₀') s') (.block H.exit)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.Pbk.kregs) (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.X86_64.Pbk.kr_agree hq h.1.kr h.2.kr)) hx
  exact RelCT.assoc ((VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_rel hp hp' hz hq hc).seq ((VG.Proof.Pbkdf2.Md.X86_64.Pbk.key_rel hH hp hp' hz hq hc).seq
    ((VG.Proof.Pbkdf2.Md.X86_64.Pbk.setup_rel hH hp hp' hz hq hc hIn hInsp hInd).seq
      (lr.seq ((VG.Proof.Pbkdf2.Md.X86_64.Pbk.loop_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId).seq ex)))))

end

/-- `pbkdf2` is verified against `pbkG`, given the taint checks, the proofs
of the functions it calls, and the facts about its code that the kernel
checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) (hz : PSizes H) (hc : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Checks H)
    (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hInsp : NoSp H.hmacInit)
    (hInd : H.hmacInit.depth ≤ 2)
    (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    (hmx : H.pbkdf2.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (pbkG hH.SH (H.W + H.S)).pre s) :
    Verified X86_64.target H.pbkdf2 (pbkG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := VG.Proof.Pbkdf2.Md.X86_64.Pbk.correct (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pre_of hH hs) hz hH hIn hInsp hInd hF hFsp hFd hI hIsp hId
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
    exact (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ct hH (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pre_of hH h₁) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pre_of hH h₂) hz ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hc hF hFsp hFd hI hIsp
      hId hIn hInsp hInd _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.HmacInit`. -/
section

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `init`

HMAC's `init` (`Impl/Pbkdf2/Md/X86_64.lean`) saves our caller's registers
(`pro_ok`), sets each state's hash value with the streaming `init`
(`callInit_ok`), writes `K₀ ⊕ ipad` into the inner state's buffer and
`K₀ ⊕ opad` into the outer one's (`keys_ok`: `ipad` a word at a time, the
key's bytes XORed in, then the outer buffer from the inner one a word at a
time), compresses each buffer into its state's hash value (`cmp_ok`), and
loads our caller's registers back. A state whose initial hash value has
absorbed the block in its buffer represents that block
(`Md.repr_block`). Constant time: the taint analysis checks the pieces
between the calls (`Checks`); the calls are constant time by the callees'
own proofs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacInit

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat zx_ofNat wp_mov wp_mov32i wp_addi wp_mov32m wp_store32
  wp_store8 wp_movzx8 wp_cmp wp_test Upd CallOk compressAt_ok compressAt_rel ea_at ofInt_natCast setWidth32
  ofNat_succ sub_beq)
open VG.Impl.MdStream.X86_64 (compressAt at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash byteAt)
open VG.Proof.Pbkdf2.X86_64 (ea_off)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG rel_taint rel_wp init_call init_rel SavedRegs saveR save_ok
  restore_ok count_loop ea_byteAt sx_one wp_xor32i xor_byte PubEq args repr_keep)
open VG.Proof.Hmac.Generic.Common (K0 K0_length covers_one InRegions.right' bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' bytesAt_writeBytes_sep)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Pbkdf2.MdKeys (ipadBlk ipadBlk_length ipadBlk_zero ipadBlk_succ ipadBlk_eq writeBytes_set fill_mem
  xorOpad_mem xorOpad_ipad)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀, H.S⟩
abbrev outR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀, H.S⟩
abbrev keyR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The compression function's working space. -/
abbrev calR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀, H.P.so⟩
/-- Where our caller's registers are saved. -/
abbrev svR : Region := saveR H.stream (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀)
/-- The buffer of the state at `p`. -/
abbrev bufOf (p : Addr) : Addr := p + BitVec.ofNat 64 H.P.N
/-- The key, padded to a block. -/
abbrev k0 : List Byte := VG.Proof.Hmac.Generic.Common.K0 s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀) H.P.B

end

abbrev scR (sc : Nat) (s₀ : State) : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀, 8 * sc⟩

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀ ≤ H.P.B
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀)
  i_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀)
  o_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀)
  k_i : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀)
  k_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀)
  k_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀)
  ret_i : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀)
  ret_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀)
  ret_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀)
  stk_i : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀)
  stk_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀)
  stk_k : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀)
  stk_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀)
  nw : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.stream.buf ≤ 8 * sc

variable {H : Hash} (hH : HashOK H)

theorem pre_of {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.stream.buf ≤ 8 * sc) :
    VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit⟩

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.P.N ≤ 64 ∧ 0 < H.P.B ∧ H.P.B ≤ 128 ∧
    H.P.so + 48 = 8 * H.stream.W ∧ H.stream.buf = 8 * H.stream.W + 48 ∧ H.stream.W ≤ 256 ∧
    8 * H.stream.W + 48 ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 := by
  have := hH.hN4; have := hH.N_le; have := hH.B_le; have := hH.B_pos; have := hH.hso; have := hp.nw
  have := hp.fits
  have hb : H.stream.buf = 8 * H.stream.W + 48 := rfl
  have hw : H.stream.W = (H.P.so + 48) / 8 := rfl
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega
  omega

/-! ## The parts of the regions -/

theorem save_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.svR H s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  exact Offset.sub_base _ h

theorem cal_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.calR H s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  exact Region.sub_prefix (by omega)

theorem cal_save : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.calR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.svR H s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', h''⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  have := hp.nw
  exact Offset.base_disjoint _ (by omega) (by omega)

omit hH hp in
theorem stk_ret : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega)

/-- What a state's region is: writable, and apart from the others. -/
structure StOk (p : Addr) : Prop where
  mem : ⟨p, H.S⟩ ∈ s₀.wr
  sc : Region.Disjoint ⟨p, H.S⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀)
  stk : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀).Disjoint ⟨p, H.S⟩
  ret : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀).Disjoint ⟨p, H.S⟩
  key : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀).Disjoint ⟨p, H.S⟩

omit hH in
theorem stOk_in : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) :=
  ⟨by rw [hp.wr]; simp, hp.i_s, hp.stk_i, hp.ret_i, hp.k_i⟩

omit hH in
theorem stOk_out : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) :=
  ⟨by rw [hp.wr]; simp, hp.o_s, hp.stk_o, hp.ret_o, hp.k_o⟩

/-- A region the code may write while our caller's registers, the return
address and the key stay put. -/
structure Away (r : Region) : Prop where
  sv : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.svR H s₀).Disjoint r
  ret : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀).Disjoint r
  key : (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀).Disjoint r

theorem away_st {p : Addr} (hs : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {r : Region}
    (h : Region.Sub r ⟨p, H.S⟩) : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Away (H := H) (s₀ := s₀) r :=
  ⟨(hs.sc.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.save_sub hH hp)).sub_right h, hs.ret.sub_right h, hs.key.sub_right h⟩

theorem away_cal : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Away (H := H) (s₀ := s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.calR H s₀) :=
  ⟨(VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_save hH hp).symm, hp.ret_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_sub hH hp), hp.k_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_sub hH hp)⟩

theorem away_stk {r : Region} (h : Region.Sub r (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀)) : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Away (H := H) (s₀ := s₀) r :=
  ⟨(hp.stk_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.save_sub hH hp)).sub_right h, stk_ret.symm.sub_right h, hp.stk_k.symm.sub_right h⟩

end

/-! ## What holds from the prologue on -/

/-- The registers and memory kept from the prologue on, with `rbx = b` (the
state being compressed). -/
structure KR (H : Hash) (s₀ : State) (b : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = b
  rbp : s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀
  r12 : s.gpr .r12 = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx
  r15 : s.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀
  saved : SavedRegs H.stream (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  key : ∀ i < VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀, s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀ + BitVec.ofNat 64 i)

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} {b : Addr} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Away (H := H) (s₀ := s₀) r) : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.rbp, (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13,
    (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf fun r hr => (ha r hr).sv,
    (hf.readW (r := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀) (Region.contains_self _ _) (fun r hr => (ha r hr).ret) (by decide)).trans h.ret,
    fun i hi => (hf.bytes (R := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀) (fun r hr => (ha r hr).key) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
      hi).trans (h.key i hi)⟩

theorem KR.regs {s₀ s s' : State} {b : Addr} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s' :=
  h.keep (rs := []) hrd hwr hg (by rw [hm]; exact Frame.refl _ _) (by simp)

/-! ## The prologue -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀)
include hH hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hL, -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  unfold Hash.initPrologue
  refine save_ok H.stream (scr := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀) rfl hW (by rw [hp.wr]; simp) hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2.2.2.2, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1, u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have hs : ∀ r ∈ [VG.Proof.Pbkdf2.Md.X86_64.HmacInit.svR H s₀], (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀).Disjoint r ∧ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨hp.ret_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.save_sub hH hp), hp.k_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.save_sub hH hp)⟩
  exact ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    g _ (by decide),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    hm ▸ sv₁,
    by rw [hm]; exact f₁.readW (r := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.retR s₀) (Region.contains_self _ _) (fun r hr => (hs r hr).1) (by decide),
    fun i hi => by
      rw [hm]; exact f₁.bytes (R := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keyR s₀) (fun r hr => (hs r hr).2) (Nat.le_of_lt (s₀.gpr .rcx).isLt) hi⟩

end

/-! ## The calls of the streaming `init` -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀)
include hH hp

/-- A call of the streaming `init` on the state at `p`, from the register `st`. -/
theorem callInit_ok {b : Addr} {s : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hst : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s' → Frame [⟨p, H.S⟩, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.stream.callInit st) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => WP.block_nil ?_)
  have k₁ : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s₁ := hk.regs u₁.rd u₁.wr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem
  refine init_call hH.stream (st := p) (by rw [u₁.gpr, hs]) (by rw [k₁.wr]; exact covers_one hst.mem)
    (by rw [k₁.rsp]; exact hst.stk) fun s' ha hr => ?_
  have f := ha.frame
  rw [k₁.rsp, u₁.mem] at f
  refine hQ s' (k₁.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) (u₁.mem ▸ f) ?_) f hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_st hH hp hst (fun _ h => h)
  · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_stk hH hp (fun _ h => h)

end

/-! ## The padded keys -/

/-- Stores of `ipad` words (the low 32 bits of `rax`) at `rbx + o + 4 k`, for
`k < n`, which write `4 n` bytes of `ipad` from `p = rbx + o`. -/
theorem fill_ok {o : Nat} {p : Addr} : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .rbx + BitVec.ofNat 64 o = p → (s.gpr .rax).setWidth 32 = 0x36363636 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (4 * k)) 4) → 4 * n + 4 < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem p (List.replicate (4 * n) ipad) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store32 (at_ .rbx (o + 4 * k)) .rax) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hp hax hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hp hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_store32 (a := p + BitVec.ofNat 64 (4 * n)) (by rw [ea_off, g₁, hp])
      (by rw [wr₁]; exact hout n (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ =>
        k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_
    rw [m₂, g₁, hax, m₁, fill_mem _ _ _ (by omega), Nat.mul_succ]

/-- After `j` bytes of the key at `K` (whose bytes are those of `mk`), from the
state `s` the loop starts in: the buffer at `P` holds `ipadBlk … j` over `m`. -/
structure KeyInv (s : State) (m mk : Mem) (P K : Addr) (B j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = VG.WriteBytes.writeBytes m P (ipadBlk mk K B j)

/-- Where the key loop reads and writes. -/
structure KeyRegs (H : Hash) (s : State) (m mk : Mem) (P K : Addr) (kl : Nat) : Prop where
  kl_le : kl ≤ H.P.B
  hB : H.P.B ≤ 128
  rbp : s.gpr .rbp = K
  rbx : s.gpr .rbx + BitVec.ofNat 64 H.P.N = P
  r13 : s.gpr .r13 = BitVec.ofNat 64 kl
  key : ∀ i < kl, m (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i)
  kin : ∀ i < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1
  bout : ∀ i < H.P.B, InRegions s.wr (P + BitVec.ofNat 64 i) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, H.P.B⟩

theorem key_step {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyRegs H s m mk P K kl) {j : Nat}
    (hj : j < kl) {t : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyInv s m mk P K H.P.B j t) :
    WP isa (.block [.movzx8 .rax (byteAt .rbp 0), .alu32 .xor .rax (.imm 0x36),
      .store8 (byteAt .rbx H.P.N) .rax, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]) t
      fun t' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyInv s m mk P K H.P.B (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hr.kl_le
  have hB := hr.hB
  have hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = mk (K + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hr.key j hj]
    refine (VG.WriteBytes.writeBytes_frame m P _ (R := ⟨P, H.P.B⟩) (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨K, kl⟩) ?_ (by show kl ≤ 2 ^ 64; omega) hj
    simp only [List.mem_singleton]; rintro r rfl; exact hr.disj
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide), hr.rbp, BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hr.kin j hj) fun t₁ u₁ => ?_
  refine wp_xor32i fun t₂ u₂ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ j (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r14]),
      u₂.other _ (by decide), u₁.other _ (by decide), h.other _ (by decide) (by decide), hr.rbx])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hr.bout j (by omega)) fun t₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_cmp fun t₅ g₅ m₅ rd₅ wr₅ _ z₅ => WP.block_nil ?_
  have h14 : t₄.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [u₄.gpr, g₃, u₂.other _ (by decide), u₁.other _ (by decide), h.r14, sx_one, ofNat_succ]
  refine ⟨⟨by rw [rd₅, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₅, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 => by rw [g₅, u₄.other r h2, g₃, u₂.other r h1, u₁.other r h1, h.other r h1 h2],
    by rw [g₅, h14], ?_⟩, ?_⟩
  · have v : (t₂.gpr .rax).setWidth 8 = mk (K + BitVec.ofNat 64 j) ^^^ ipad := by
      rw [u₂.gpr, u₁.gpr, xor_byte, hbyte]; rfl
    rw [m₅, u₄.mem, m₃, v, u₂.mem, u₁.mem, h.mem, writeBytes_set _ _ _ (by rw [hl]; omega) (by rw [hl]; omega),
      ipadBlk_succ]
  · rw [z₅, h14, show t₄.gpr .r13 = BitVec.ofNat 64 kl by
      rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide),
        h.other _ (by decide) (by decide), hr.r13], sub_beq (by omega) (by omega)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyRegs H s m mk P K kl)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hz : s.zf = some (decide (kl = 0)))
    (hm : s.mem = VG.WriteBytes.writeBytes m P (ipadBlk mk K H.P.B 0)) :
    WP isa (.ite .e (.block []) H.keyLoop) s (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyInv s m mk P K H.P.B kl) := by
  have i0 : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyInv s m mk P K H.P.B 0 s := ⟨rfl, rfl, fun _ _ _ => rfl, h14, hm⟩
  refine WP.ite (decide (kl = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyInv s m mk P K H.P.B) (fun j hj t h => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.key_step hr hj h) i0

/-- The words of the outer buffer: `n` words of the inner buffer at
`rbx + N`, XORed with `ipad ⊕ opad`, to `r12 + N`. -/
theorem opad_ok : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (4 * n) (s.gpr .r12 + BitVec.ofNat 64 H.P.N) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .r12 + BitVec.ofNat 64 H.P.N)
        ((bytesAt s.mem (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁ _ (by decide)]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_xor32i fun s₃ u₃ => ?_
    refine wp_store32 (a := s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    rw [m₄, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, setWidth32, setWidth32, m₁, Nat.mul_succ,
      xorOpad_mem _ _ _ _ (by rwa [← Nat.mul_succ]) (by omega)]

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀)
include hH hp

/-- `K₀ ⊕ ipad` into the inner buffer and `K₀ ⊕ opad` into the outer one, and
the inner block's address in `rsi`. -/
theorem keys_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s) :
    WP isa H.initKeys s fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) t ∧ t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) ∧
      Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀), H.P.B⟩, ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀), H.P.B⟩] s.mem t.mem ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) ipad ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) opad := by
  obtain ⟨hN4, hB4, hN, hB0, hB, -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  have hkl := hp.kl_le
  have eB : 4 * (H.P.B / 4) = H.P.B := by omega
  have si := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_in (H := H) hp
  have so := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_out (H := H) hp
  have bI : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀), H.P.B⟩ ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀), H.P.B⟩ ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hS : H.S = H.P.N + H.P.B := rfl
  have inI : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, si.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have inO : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, so.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dIO : Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀), H.P.B⟩ ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀), H.P.B⟩ :=
    (hp.i_o.sub_left bI).sub_right bO
  unfold Hash.initKeys Hash.ipadFill
  simp only [List.cons_append]
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => ?_)
  refine VG.Proof.Pbkdf2.Md.X86_64.HmacInit.fill_ok (o := H.P.N) (p := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) (H.P.B / 4) _ s₁ _ (by rw [u₁.other _ (by decide), hk.rbx])
    (by rw [u₁.gpr, setWidth32]) (fun k hk' => by rw [u₁.wr, hk.wr]; exact inI _ 4 (by omega)) (by omega)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => wp_test fun s₄ g₄ m₄ rd₄ wr₄ z₄ => WP.block_nil ?_
  have G₄ : ∀ r, r ≠ .rax → r ≠ .r14 → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₄, u₃.other r h2, g₂, u₁.other r h1]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, u₃.rd, rd₂, u₁.rd, hk.rd]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, u₃.wr, wr₂, u₁.wr, hk.wr]
  have hr : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KeyRegs H s₄ s.mem s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀) :=
    { kl_le := hkl, hB := hB
      rbp := by rw [G₄ _ (by decide) (by decide), hk.rbp]
      rbx := by rw [G₄ _ (by decide) (by decide), hk.rbx]
      r13 := by rw [G₄ _ (by decide) (by decide), hk.r13, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      key := hk.key
      kin := fun i hi => by
        rw [rd₄', wr₄', hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          Offset.contains_base _ (by omega) (by omega)⟩
      bout := fun i hi => by rw [wr₄']; exact inI i 1 (by omega)
      disj := hp.k_i.sub_right bI }
  have h14 : s₄.gpr .r14 = BitVec.ofNat 64 0 := by rw [g₄, u₃.gpr]; rfl
  have hz : s₄.zf = some (decide (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀ = 0)) := by
    rw [z₄, u₃.other _ (by decide), g₂, u₁.other _ (by decide), hk.r13, BitVec.and_self]
    congr 1
    by_cases h : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀ = 0
    · simp [h, BitVec.eq_of_toNat_eq (show (s₀.gpr .rcx).toNat = (0 : BitVec 64).toNat from h)]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'; exact h (by show (s₀.gpr .rcx).toNat = 0; rw [h']; rfl)
  have hm : s₄.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) (ipadBlk s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀) H.P.B 0) := by
    rw [m₄, u₃.mem, m₂, u₁.mem, ipadBlk_zero, eB]
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.key_ok hr h14 hz hm) fun t ht => ?_)
  have Gt : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ht.other r h1 h2, G₄ r h1 h2]
  have bxt : t.gpr .rbx = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀ := by rw [Gt _ (by decide) (by decide), hk.rbx]
  have r12t : t.gpr .r12 = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀ := by rw [Gt _ (by decide) (by decide), hk.r12]
  have rdt : t.rd = s₀.rd := by rw [ht.rd, rd₄']
  have wrt : t.wr = s₀.wr := by rw [ht.wr, wr₄']
  unfold Hash.opadFill
  refine VG.Proof.Pbkdf2.Md.X86_64.HmacInit.opad_ok (H.P.B / 4) _ t _
    (fun k hk' => by rw [bxt, rdt, wrt]; exact InRegions.right' (inI _ 4 (by omega)))
    (fun k hk' => by rw [r12t, wrt]; exact inO _ 4 (by omega))
    (by rw [bxt, r12t, eB]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega)
    fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  refine wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => WP.block_nil ?_
  rw [bxt, r12t, eB] at m₅
  have G : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .rsi → s₇.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₇.other r h3, u₆.other r h3, g₅ r h1, Gt r h1 h2]
  have hm₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  have lI : (ipadBlk s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀) H.P.B (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀)).length = H.P.B := ipadBlk_length _ _ _ _
  have bt : bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) ipad := by
    rw [ht.mem, bytesAt_writeBytes_self' lI (by omega), ipadBlk_eq _ _ hkl]
  have lO : ((bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length = H.P.B := by
    simp [bytesAt]
  have fT : Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀), H.P.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [lI]; exact Region.contains_self _ _)
  have f₅ : Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀), H.P.B⟩] t.mem s₅.mem := by
    rw [m₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [lO]; exact Region.contains_self _ _)
  have f : Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀), H.P.B⟩, ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀), H.P.B⟩] s.mem s₇.mem := by
    rw [hm₇]; exact (fT.mono (by simp)).trans (f₅.mono (by simp))
  refine ⟨hk.keep (by rw [u₇.rd, u₆.rd, rd₅, ht.rd, rd₄, u₃.rd, rd₂, u₁.rd])
      (by rw [u₇.wr, u₆.wr, wr₅, ht.wr, wr₄, u₃.wr, wr₂, u₁.wr]) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact G _ (by decide) (by decide) (by decide)) f
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_st hH hp si bI
        · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_st hH hp so bO),
    by rw [u₇.gpr, u₆.gpr, g₅ _ (by decide), bxt, sx_ofNat (by omega)], f, ?_, ?_⟩
  · have sIO : Mem.Sep (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) H.P.B (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀))
        ((bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length := by
      rw [lO]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [hm₇, m₅, bytesAt_writeBytes_sep _ _ sIO (by omega), bt]
  · rw [hm₇, m₅, bytesAt_writeBytes_self' lO (by omega), bt, xorOpad_ipad]

/-! ## The compressions -/

/-- What the call of the compression function needs, for the state at `p`. -/
theorem callOk {p : Addr} (hs : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ p t)
    (hsi : t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p) : CallOk H.P t p (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p) := by
  obtain ⟨-, -, hN, -, hB, hso, -, -, hL, h8⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  have sR : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hv : Region.Sub ⟨p, H.P.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hb : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p, H.P.B⟩ ⟨p, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hc : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr s₀, H.P.so⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀) := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_sub hH hp
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨hk.rbx, hk.r15, hsi, (hs.sc.sub_left hv).sub_right hc,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hs.sc.sub_left hb).sub_right hc,
    (hs.stk.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hc,
    (hs.stk.sub_left b8).sub_right hb, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hs.mem, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ hs.mem, 0, (BitVec.add_zero _).symm,
        by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hs.mem, 0, (BitVec.add_zero _).symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩

/-- The compression of the block in the buffer of the state at `p` into its
hash value. -/
theorem cmp_ok {p : Addr} (hs : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ p t)
    (hsi : t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ p s' → Frame [⟨p, H.P.N⟩, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.calR H s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀] t.mem s'.mem →
      hH.md.stateAt s'.mem p = hH.md.compress (hH.md.stateAt t.mem p) (hH.md.blockAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p)) →
      Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega) (by omega)
  refine compressAt_ok hH.md hH.comp (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callOk hH hp hs hk hsi) (by omega) (by omega)
    fun s' hrd hwr hcs hfr hst _ _ => ?_
  have f : Frame [⟨p, H.P.N⟩, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.calR H s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀] t.mem s'.mem := hfr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.calR H s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stkR s₀, by simp, b8⟩
  refine k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_) f hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_st hH hp hs (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega))
  · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_cal hH hp
  · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_stk hH hp (fun _ h => h)

/-- From the inner state to the outer one. -/
theorem mid_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s) :
    WP isa (.block H.initOuter) s fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) t ∧ t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) ∧
      t.mem = s.mem := by
  obtain ⟨-, -, hN, -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  unfold Hash.initOuter
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => WP.block_nil ?_
  have G : ∀ r, r ≠ .rbx → r ≠ .rsi → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, hk.rd], by rw [u₃.wr, u₂.wr, u₁.wr, hk.wr],
    by rw [G _ (by decide) (by decide), hk.rsp],
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.r12],
    by rw [G _ (by decide) (by decide), hk.rbp], by rw [G _ (by decide) (by decide), hk.r12],
    by rw [G _ (by decide) (by decide), hk.r13], by rw [G _ (by decide) (by decide), hk.r15],
    by rw [hm]; exact hk.saved, by rw [hm]; exact hk.ret, fun i hi => by rw [hm]; exact hk.key i hi⟩,
    by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r12, sx_ofNat (by omega)], hm⟩

/-! ## Correctness -/

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀)) = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀ := by
  have := hp.kl_le
  simp only [blockKey, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0, VG.Proof.Hmac.Generic.Common.K0, bytesAt_length, hH.hB, show ¬ (H.P.B < VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kl s₀) by omega, ↓reduceIte]

theorem correct : WP isa H.hmacInit s₀ fun s' => gprPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  obtain ⟨-, -, hN, hB0, hB, -, -, hW, hL, -⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.sizes hH hp
  have hkl := hp.kl_le
  have si := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_in (H := H) hp
  have so := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_out (H := H) hp
  have hsc : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.pro_ok hH hp) fun s₁ k₁ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callInit_ok hH hp k₁ (st := .rbx) k₁.rbx si fun s₂ k₂ f₂ r₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callInit_ok hH hp k₂ (st := .r12) k₂.r12 so fun s₃ k₃ f₃ r₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keys_ok hH hp k₃) fun s₄ ⟨k₄, si₄, f₄, bI₄, bO₄⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cmp_ok hH hp si k₄ si₄ fun s₅ k₅ f₅ e₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.mid_ok hH hp k₅) fun s₆ ⟨k₆, si₆, m₆⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cmp_ok hH hp so k₆ si₆ fun s₇ k₇ f₇ e₇ => ?_)
  refine WP.mono (restore_ok H.stream k₇.r15 hW k₇.saved (by rw [k₇.wr]; exact hsc) hL)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₇.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₇.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  -- What each piece keeps: the hash values and the buffers it does not write.
  have keepS : ∀ {rs : List Region} {m m' : Mem} {p : Addr}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) → hH.md.stateAt m' p = hH.md.stateAt m p :=
    fun hf hd => hH.md.stateAt_congr fun i hi =>
      hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega) hi
  have hvI : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀, H.P.N⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hvO : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀, H.P.N⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have bI : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀), H.P.B⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀), H.P.B⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have nb : ∀ p : Addr, Region.Disjoint ⟨p, H.P.N⟩ ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p, H.P.B⟩ := fun p =>
    Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  have iv : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := ((hH.repr _ _ _).1 h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  -- The inner state.
  have iv₄ : hH.md.stateAt s₄.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact nb _
        · exact (hp.i_o.sub_left hvI).sub_right bO),
      keepS f₃ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.i_o.sub_left hvI
        · exact hp.stk_i.symm.sub_left hvI), iv r₂]
  have hl : (xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) ipad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rI₅ := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl bI₄ (e₅.trans (congrArg (hH.md.compress · _) iv₄))
  -- The outer state.
  have iv₆ : hH.md.stateAt s₆.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) = hH.iv := by
    rw [m₆, keepS f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right hvI
        · exact (so.sc.sub_left hvO).sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_sub hH hp)
        · exact so.stk.symm.sub_left hvO),
      keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right bI
        · exact nb _), iv r₃]
  have bO₆ : bytesAt s₆.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) opad := by
    rw [m₆, bytes_keep f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact (hp.i_o.symm.sub_left bO).sub_right hvI
        · exact (so.sc.sub_left bO).sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_sub hH hp)
        · exact so.stk.symm.sub_left bO) (by omega), bO₄]
  have hl' : (xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) opad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rO₇ := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl' bO₆ (e₇.trans (congrArg (hH.md.compress · _) iv₆))
  -- The inner state, kept by the outer compression.
  have rI₇ : hH.SH.Repr s₇.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) (xorPad (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.k0 H s₀) ipad) :=
    VG.Proof.Pbkdf2.Md.X86_64.Calls.repr_keep hH.stream f₇ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hp.i_o.sub_right hvO
      · exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cal_sub hH hp)
      · exact hp.stk_i.symm) (m₆ ▸ (hH.repr _ _ _).2 rI₅)
  show hH.SH.Repr s'.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) _ ∧ hH.SH.Repr s'.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) _
  rw [hm, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.blockKey_eq hH hp]
  exact ⟨rI₇, (hH.repr _ _ _).2 rO₇⟩

end

/-! ## Constant time -/

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.initPrologue) hc).isSome = true
  argI : ∀ st ∈ [Reg.rbx, .r12], ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs) (.block [.mov .rdi (.reg st)])
    hc).isSome = true
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs) H.initKeys hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs) (.block H.initOuter) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs) (.block H.stream.restore) hc).isSome = true

section
variable {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀) (hp' : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc s₀') (hq : VG.Proof.Pbkdf2.Md.X86_64.Calls.PubEq s₀ s₀')

omit hH in
theorem kr_agree (hq : VG.Proof.Pbkdf2.Md.X86_64.Calls.PubEq s₀ s₀') {b : Addr} {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s) (h' : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]
  · rw [h.rbp, h'.rbp, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kp, hq.rdx]
  · rw [h.r12, h'.r12, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out, hq.rsi]
  · rw [h.r13, h'.r13, hq.rcx]
  · rw [h.r15, h'.r15, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

/-- A call of the streaming `init` on the state at `p`, from `st`. -/
theorem callInit_rel (hc : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Checks H) {b : Addr} {st : Reg} (hst : st ∈ [Reg.rbx, .r12]) {p : Addr}
    (hs : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) (hs' : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') p)
    (hr : ∀ {t : State}, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b t → t.gpr st = p) (hr' : ∀ {t : State}, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b t → t.gpr st = p) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b s') (H.stream.callInit st)
      fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b s' := by
  have ha : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b s') (.block [.mov .rdi (.reg st)])
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s ∧ s.gpr .rdi = p) ∧ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b s' ∧ s'.gpr .rdi = p) :=
    rel_taint VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kr_agree hq h h') (hc.argI st hst)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr h]⟩)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr' h]⟩)
  have call : ∀ {t₀ : State}, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Pre H sc t₀ → VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := t₀) p → ∀ t, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H t₀ b t →
      t.gpr .rdi = p → WP isa (.call H.stream.initN H.stream.initC) t (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H t₀ b) := fun hpt hst t k d => by
    refine init_call hH.stream (st := p) d (by rw [k.wr]; exact covers_one hst.mem)
      (by rw [k.rsp]; exact hst.stk) fun s' ha _ => ?_
    have f := ha.frame
    rw [k.rsp] at f
    refine k.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_st hH hpt hst (fun _ h => h)
    · exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.away_stk hH hpt (fun _ h => h)
  refine ha.seq (rel_wp (F := fun s => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ b s ∧ s.gpr .rdi = p)
    (F' := fun s => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' b s ∧ s.gpr .rdi = p) (init_rel hH.stream (st := p) fun s s' h => ?_)
    (fun t ⟨k, d⟩ => call hp hs t k d) (fun t ⟨k, d⟩ => call hp' hs' t k d))
  obtain ⟨⟨k, d⟩, ⟨k', d'⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one hs.mem, by rw [k'.wr]; exact covers_one hs'.mem,
    by rw [k.rsp]; exact hs.stk, by rw [k'.rsp]; exact hs'.stk, by rw [k.rsp, k'.rsp, hq.rsp]⟩

/-- A compression of the state at `p`. -/
theorem cmp_rel {p : Addr} (hs : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p)
    (hs' : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') p) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ p s ∧ s.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p) ∧ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' p s' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H p))
      (compressAt H.compN H.compC) fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ p s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' p s' :=
  rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, si⟩, ⟨k', si'⟩⟩ =>
      ⟨⟨_, _, _, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callOk hH hp hs k si⟩, ⟨_, _, _, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callOk hH hp' hs' k' si'⟩,
        by rw [k.rbx, k'.rbx], by rw [k.r15, k'.r15, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr, VG.Proof.Pbkdf2.Md.X86_64.HmacInit.scr, hq.r8], by rw [si, si'],
        by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun s ⟨k, si⟩ => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cmp_ok hH hp hs k si fun s' k' _ _ => k')
    (fun s ⟨k, si⟩ => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cmp_ok hH hp' hs' k si fun s' k' _ _ => k')

theorem ct (hc : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have ei : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀' = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀ := hq.rdi.symm
  have eo : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀' = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀ := hq.rsi.symm
  have si := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_in (H := H) hp
  have so := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_out (H := H) hp
  have si' : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) := ei ▸ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_in (H := H) hp'
  have so' : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) := eo ▸ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.stOk_out (H := H) hp'
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s' :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.pro_ok hH hp)
      (fun _ e => by rw [e, ← ei]; exact VG.Proof.Pbkdf2.Md.X86_64.HmacInit.pro_ok hH hp')
  have c₁ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callInit_rel hH hp hp' hq hc (b := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) (st := .rbx) (by simp) si si'
    (fun k => k.rbx) (fun k => k.rbx)
  have c₂ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.callInit_rel hH hp hp' hq hc (b := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) (st := .r12) (by simp) so so'
    (fun k => k.r12) (fun k => by rw [k.r12, eo])
  have keys : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s') H.initKeys
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s ∧ s.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀)) :=
    rel_taint VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kr_agree hq h h') hc.keys
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keys_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.keys_ok hH hp' (ei ▸ h)) fun _ h => ⟨ei ▸ h.1, by rw [h.2.1, ei]⟩)
  have mid : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.inn s₀) s') (.block H.initOuter)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) s ∧ s.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀)) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) s' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀)) :=
    rel_taint VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kr_agree hq h h') hc.mid
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.mid_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.mid_ok hH hp' (ei ▸ h)) fun _ h => ⟨eo ▸ h.1, by rw [h.2.1, eo]⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.out s₀) s') (.block H.stream.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kregs) (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.kr_agree hq h.1 h.2)) hr
  exact pro.seq (c₁.seq (c₂.seq (keys.seq ((VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cmp_rel hH hp hp' hq si si').seq (mid.seq
    ((VG.Proof.Pbkdf2.Md.X86_64.HmacInit.cmp_rel hH hp hp' hq so so').seq restore))))))

end

/-- HMAC's `init` is verified against `initG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86_64.HmacInit.Checks H) (hfit : H.stream.buf ≤ 8 * sc)
    (hmx : H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacInit.correct hH (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.pre_of hH hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.ct hH (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.pre_of hH h₁ hfit) (VG.Proof.Pbkdf2.Md.X86_64.HmacInit.pre_of hH h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.HmacFin`. -/
section

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `finalize`

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86_64.lean`) starts by finalizing the
inner state into `scratch` (`Proof/Pbkdf2/Md/X86_64/HmacFinInner.lean`);
then it computes the outer hash with one compression, as `iterate`
does (`Proof/Pbkdf2/X86_64/Iterate.lean`): it writes the outer hash value over
the inner state's and, into its buffer, the inner digest and the padding
(`finMid`, `mid_ok`), compresses that block (`cmp_ok`) and writes the digest
of the result to `out` (`finOut`, `out_ok`). That this is the outer hash is
`Md.Link.hash_block`. Everything up to the inner digest is
`HmacFinInner.lean`'s, for the hash function's streaming functions
(`HashOK.stream`); constant time likewise, from the taint checks of the pieces between the calls
(`Checks`) and the compression function's own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacFin

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat wp_mov wp_addi CallOk compressAt_ok compressAt_rel)
open VG.Impl.MdStream.X86_64 (compressAt)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.X86_64 (padLen_ok)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (finG FinArgs rel_taint rel_wp fin_rel restore_ok SavedRegs saveR repr_keep
  PubEq args)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The registers the code after the inner digest keeps public: `inner`,
the block (its buffer), `out`, `scratch` and the stack pointer. -/
abbrev oregs : List Reg := [.rbx, .rbp, .r13, .r15, .rsp]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs) (.block (fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacFin.oregs) (.block H.finOut) hc).isSome = true

/-- The block: the inner state's buffer. -/
abbrev blk (H : Hash) (s₀ : State) : Addr := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 H.P.N

/-- What holds from the outer block on: as `KR`, but `outer` is no longer
needed. -/
structure KO (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀
  r13 : s.gpr .r13 = op s₀
  r15 : s.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀
  saved : SavedRegs H.stream (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

theorem KO.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r13, .r15, .rsp], s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.stream (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint r) : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf hs,
    (hf.readW (r := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.P.L % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.D + H.P.L + 4 ≤ H.P.B ∧
    0 < H.D ∧ H.D ≤ H.P.N ∧ H.P.N + H.P.L ≤ H.P.B ∧ H.P.B ≤ 128 ∧ H.P.so + 96 + H.P.N ≤ 8 * sc ∧
    8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 := by
  have hH_hN4 := hH.hN4; have hH_hD4 := hH.hD4; have hH_hL4 := hH.hL4; have hH_hDL := hH.hDL; have hH_hD0 := hH.hD0; have hH_hDN := hH.hDN
  have hH_hNL := hH.hNL; have hH_B_le := hH.B_le; have hH_hso := hH.hso; have hp_nw := hp.nw; have hp_hS := hp.hS
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega_using [h]
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hb : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 48 := rfl
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  omega

omit hH hp in
/-- The ranges of the inner state, which holds the hash value and the block. -/
theorem in_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H.stream) s₀) :=
  Offset.sub_base _ h

omit hH in
theorem save_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (saveR H.stream (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)).Disjoint ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)).sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.in_inR h)

omit hH in
theorem ret_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  hp.ret_i.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.in_inR h)

omit hH in
/-- `KO` from `KR`, after code that writes only the inner state. -/
theorem KO.of_kr {s s' : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r13, .r15, .rsp], s'.gpr r = s.gpr r)
    (hf : Frame [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H.stream) s₀] s.mem s'.mem) : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s' :=
  KO.keep (s := s) ⟨hk.rd, hk.wr, hk.rsp, hk.rbx, hk.r13, hk.r15, hk.saved, hk.ret⟩ hrd hwr hg hf
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_i)

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and the block's address in `rsi`. -/
theorem mid_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ t ∧ t.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ ∧ t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ ∧
      (∀ i < H.P.N, t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 i) = s.mem (outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) H.D = bytesAt s.mem (T (H := H.stream) s₀) H.D ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.md.tailPad H.D := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, -, h8, hSB⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have hbuf : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have eN : 4 * (H.P.N / 4) = H.P.N := by omega
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oR : outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀) := Offset.sub_base _ (by omega_using [hbuf, hDN])
  simp only [Hash.finMid, List.append_assoc]
  refine copy32_ok (src := .r12) (dst := .rbx) (by decide) (by decide) 0 0 (H.P.N / 4) _ s _
    (fun j hj => by
      rw [hk.r12, add_ofNat]
      exact ⟨_, oR, Offset.contains_base _ (by omega_using [hj, hS]) (by omega_using [hj, hB, hNL])⟩)
    (fun j hj => by
      rw [hk.rbx, add_ofNat, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hk.r12, hk.rbx, eN]
      exact hp.i_o.symm.sep (Offset.contains_base _ (by omega_using [hS]) (by omega))
        (Offset.contains_base _ (by omega_using [hS]) (by omega)))
    (by omega_using [hB, hNL]) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [hk.r12, hk.rbx, eN, z, z] at m₁
  have r15 : s₁.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀ := by rw [g₁ _ (by decide), hk.r15]
  have rbx : s₁.gpr .rbx = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ := by rw [g₁ _ (by decide), hk.rbx]
  refine copy32_ok (src := .r15) (dst := .rbx) (by decide) (by decide) H.stream.buf H.P.N (H.D / 4) _ s₁ _
    (fun j hj => by
      rw [r15, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega_using [hj, hbuf, hDN]) (by omega_using [hj, hbuf, h8, hDN])⟩)
    (fun j hj => by
      rw [rbx, add_ofNat, wr₁, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [hj, hS, hDL]) (by omega_using [hj, hB, hNL, hDL])⟩)
    (by
      rw [r15, rbx, eD]
      exact hp.i_s.symm.sep (Offset.contains_base _ (by omega) (by omega_using [hbuf, h8, hDN, hD0]))
        (Offset.contains_base _ (by omega_using [hS, hDL]) (by omega_using [hB, hNL])))
    (by omega_using [hB, hDL]) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  rw [r15, rbx, eD] at m₂
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => ?_
  have rbp₄ : s₄.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ := by
    rw [u₄.gpr, u₃.gpr, g₂ _ (by decide), rbx, sx_ofNat (by omega_using [hB, hNL])]
  have G₄ : ∀ r, r ≠ .rax → r ≠ .rbp → s₄.gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [u₄.other r h2, u₃.other r h2, g₂ r h1]
  refine padLen_ok hH.shape (hH.lenOk _ (by omega_using [hB, hDL])) hD4 hL4 hB4 (by omega_using [hDL]) hB (s := s₄) rbp₄
    (by rw [G₄ _ (by decide) (by decide), rbx, add_ofNat,
      show H.P.N + (H.P.B - H.P.L) = H.P.N + H.P.B - H.P.L by omega_using [hDL]])
    (fun a n h' => by
      rw [u₄.wr, u₃.wr, wr₂, wr₁, hk.wr, add_ofNat]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [h', hS]) (by omega_using [h', hB, hNL])⟩) fun s₅ g₅ rd₅ wr₅ f₅ p₅ d₅ => ?_
  refine wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have G : ∀ r, r ≠ .rax → r ≠ .rbp → r ≠ .r12 → r ≠ .rsi → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₆.other r h4, g₅ r h1 h3, G₄ r h1 h2, g₁ r h1]
  have hm : s₆.mem = s₅.mem := u₆.mem
  -- What each piece writes.
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀, H.P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₂ : Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  rw [f₄] at f₅ d₅
  have fI : Frame [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H.stream) s₀] s.mem s₆.mem := by
    rw [hm]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hS])⟩
    · exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.in_inR (by omega_using [hDL])⟩
    · exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.in_inR (by omega)⟩
  refine ⟨KO.of_kr hp hk (by rw [u₆.rd, rd₅, u₄.rd, u₃.rd, rd₂, rd₁])
      (by rw [u₆.wr, wr₅, u₄.wr, u₃.wr, wr₂, wr₁])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact G _ (by decide) (by decide) (by decide) (by decide)) fI,
    by rw [u₆.other _ (by decide), g₅ _ (by decide) (by decide), rbp₄],
    by rw [u₆.gpr, g₅ _ (by decide) (by decide), rbp₄], fun i hi => ?_, ?_, by rw [hm]; exact p₅⟩
  · -- The hash value: the outer one, which the later pieces keep.
    have hd : ∀ {a n : Nat}, H.P.N ≤ a → a + n ≤ H.P.N + H.P.B →
        ∀ r ∈ [(⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ : Region)], Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀, H.P.N⟩ r := fun ha hn => by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ ha (by omega_using [hn, hB, hNL])
    rw [hm, f₅.bytes (R := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega)) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      f₂.bytes (R := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega_using [hDL])) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hB, hNL]),
      bytesAt_getD' _ _ hi]
  · -- The inner digest.
    rw [hm, d₅, m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hB, hDL])]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm.sub_right (Region.sub_prefix (by omega_using [hS]))) (by omega_using [hB, hDL])

/-- What the call of the compression function needs. -/
theorem callOk {t : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ t) (hsi : t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) :
    CallOk H.P t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.sizes hH hp
  have hH_hso := hH.hso
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have z : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ := BitVec.add_zero _
  have hv : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀, H.P.N⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H.stream) s₀) := Region.sub_prefix (by omega_using [hS])
  have hb : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀, H.P.B⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H.stream) s₀) := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.in_inR (by omega)
  have hs : Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀, H.P.so⟩ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀) := Region.sub_prefix (by omega_using [hf])
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨hk.rbx, hk.r15, hsi, (hp.i_s.sub_left hv).sub_right hs, Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hB, hNL]),
    (hp.i_s.sub_left hb).sub_right hs, (hp.stk_i.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hs,
    (hp.stk_i.sub_left b8).sub_right hb, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ iR, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hf]⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩

/-- The compression of the block into the hash value. -/
theorem cmp_ok {t : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ t) (hsi : t.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s' → s'.gpr .rbp = t.gpr .rbp →
      hH.md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) = hH.md.compress (hH.md.stateAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀))
        (hH.md.blockAt t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀)) → Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.sizes hH hp
  have hH_hso := hH.hso
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have z : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ := BitVec.add_zero _
  refine compressAt_ok hH.md hH.comp (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.callOk hH hp hk hsi) (by omega_using [hB]) (by omega_using [hB, hNL])
    fun s' hrd hwr hcs hfr hst _ _ => k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hfr ?_ ?_)
    (hcs _ (by simp [calleeSaved])) hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · have := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_inR hp (a := 0) (n := H.P.N) (by omega); rwa [z] at this
    · exact (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_save hH.stream hp).symm.sub_right (Region.sub_prefix (by show H.P.so ≤ H.P.so + 48; omega))
    · rw [hk.rsp]
      exact (hp.stk_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)).sub_right (Offset.sub_below _ (by omega) (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_i.sub_right (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using []))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by omega))
    · rw [hk.rsp]; exact (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stk_ret (s₀ := s₀)).symm.sub_right (Offset.sub_below _ (by omega) (by omega))

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s) (hbp : s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) :
    WP isa (.block H.finOut) s fun s' => ∃ t, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ t ∧
      bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀))).take H.D ∧ s'.mem = t.mem ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.sizes hH hp
  have hD := hp.hD
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have hdl := hH.md.digest_length (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀))
  have hL : 8 * H.stream.W + 48 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 48 := rfl
    have hp_fits := hp.fits
    omega_using [hp_fits, this]
  have fin : ∀ t, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ t → bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀))).take H.D →
      WP isa (.block H.stream.restore) t fun s' => ∃ t, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ t ∧
        bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀))).take H.D ∧ s'.mem = t.mem ∧
        (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
        (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = t.gpr r) := fun t kt bt =>
    WP.mono (restore_ok H.stream kt.r15 hp.hW kt.saved (by rw [kt.wr]; exact sR) hL)
      fun s' ⟨hm, _, _, hg, ho⟩ => ⟨t, kt, bt, hm, hg, ho⟩
  have rbx_in : InRegions (s.rd ++ s.wr) (s.gpr .rbx) H.P.N := by
    have := Offset.contains_base (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (d := 0) (n := H.P.N) (k := H.P.N + H.P.B) (by omega_using []) (by omega)
    rw [z] at this
    rw [hk.rbx, hk.rd, hk.wr]
    exact ⟨_, List.mem_append_right _ iR, this⟩
  unfold Hash.finOut
  by_cases hDN' : H.D < H.P.N
  · simp only [hDN', ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (hH.shape.out s rbx_in (by
        rw [hbp, hk.wr]; exact ⟨_, iR, Offset.contains_base _ (by omega_using [hS, hNL]) (by omega_using [hB, hNL])⟩)
      (by rw [hk.rbx, hbp]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hNL])))
      fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
    rw [hbp, hk.rbx] at m₁
    have f₁ : Frame [⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀, H.P.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₁ : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s₁ := hk.keep rd₁ wr₁ (fun r hr => g₁ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)) f₁
      (by simp only [List.mem_singleton]; rintro r rfl; exact VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_inR hp (by omega_using [hNL]))
      (by simp only [List.mem_singleton]; rintro r rfl; exact VG.Proof.Pbkdf2.Md.X86_64.HmacFin.ret_inR hp (by omega_using [hNL]))
    have b₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀))).take H.D := by
      rw [bytesAt_take _ _ (Nat.le_of_lt hDN'), m₁, bytesAt_writeBytes_self' hdl (by omega)]
    have rbp₁ : s₁.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ := by rw [g₁ _ (by decide), hbp]
    refine copy32_ok (src := .rbp) (dst := .r13) (by decide) (by decide) 0 0 (H.D / 4) _ s₁ _
      (fun j hj => by
        rw [rbp₁, add_ofNat, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
        exact ⟨_, List.mem_append_right _ iR, Offset.contains_base _ (by omega_using [hj, hS, hDL]) (by omega_using [hj, hB, hNL, hDL])⟩)
      (fun j hj => by
        rw [k₁.r13, add_ofNat, k₁.wr]
        exact ⟨_, pR, Offset.contains_base _ (by show 0 + 4 * j + 4 ≤ H.D; omega_using [hj]) (by omega_using [hj, hB, hDL])⟩)
      (by
        rw [rbp₁, k₁.r13, eD, add_ofNat]
        exact hp.i_p.sep (Offset.contains_base _ (by omega_using [hS, hDL]) (by omega_using [hB, hNL]))
          (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega) (by omega)))
      (by omega_using [hB, hDL]) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
    rw [rbp₁, k₁.r13, eD, z, z] at m₂
    refine fin s₂ (k₁.keep rd₂ wr₂ (fun r hr => g₂ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      (m₂ ▸ VG.WriteBytes.writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [bytesAt_length]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_p)) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hB, hDL]), b₁]
  · have eDN : H.D = H.P.N := by omega_using [hDN', hDN]
    simp only [hDN', ↓reduceIte, List.cons_append]
    refine wp_mov fun s₁ u₁ _ _ => ?_
    rw [WP.block_append_iff]
    have rbx₁ : s₁.gpr .rbx = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ := by rw [u₁.other _ (by decide), hk.rbx]
    refine WP.mono (hH.shape.out s₁ (by rw [u₁.rd, u₁.wr, u₁.other _ (by decide)]; exact rbx_in) (by
        rw [u₁.gpr, hk.r13, u₁.wr, hk.wr, ← eDN]; exact ⟨_, pR, Region.contains_self _ _⟩)
      (by rw [rbx₁, u₁.gpr, hk.r13, ← eDN]; exact hp.i_p.sub_left (Region.sub_prefix (by omega_using [hS, hDL]))))
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    rw [rbx₁, u₁.gpr, hk.r13, u₁.mem] at m₂
    refine fin s₂ (hk.keep (rd₂.trans u₁.rd) (wr₂.trans u₁.wr) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide), u₁.other _ (by decide)])
      (m₂ ▸ VG.WriteBytes.writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [hdl, ← eDN]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_p)) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (by omega_using [hB, hNL]), List.take_of_length_le (by omega_using [hdl])]

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => gprPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.sizes hH hp
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.pro_ok hp) fun s₁ ⟨k₁, di₁, dx₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hH.stream hp k₁ di₁ dx₁) fun t₁ ⟨kt₁, a₁, si₁, m₁⟩ =>
    finCall_ok hH.stream hp kt₁ a₁ fun s₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.mid_ok hH hp k₂) fun s₃ ⟨k₃, bp₃, si₃, i₃, b₃, p₃⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cmp_ok hH hp k₃ si₃ fun s₄ k₄ bp₄ e₄ => ?_)
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.out_ok hH hp k₄ (bp₄.trans bp₃)) fun s' ⟨s₅, k₅, m₅, hm, hg, ho⟩ =>
    ⟨⟨fun r hr => ?_, by rw [hm, k₅.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.P.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until the inner digest is written.
  have oI : ∀ r ∈ [saveR H.stream (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)
  have o₂ : ∀ r ∈ [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H.stream) s₀, tR (H := H.stream) s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.calR hH.stream s₀,
      VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_sub hH.stream hp)
    · exact hp.stk_o.symm
  have rO₂ := VG.Proof.Pbkdf2.Md.X86_64.Calls.repr_keep hH.stream f₂ o₂ (m₁ ▸ VG.Proof.Pbkdf2.Md.X86_64.Calls.repr_keep hH.stream f₁ oI hrO)
  -- The inner digest.
  have dig : (bytesAt s₂.mem (T (H := H.stream) s₀) H.P.N).take H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) :=
    d₂ _ (m₁ ▸ VG.Proof.Pbkdf2.Md.X86_64.Calls.repr_keep hH.stream f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The outer hash: one compression of the outer hash value.
  have hxl : (xorPad k0 opad).length = H.P.B := by rw [xorPad_length, hk0]
  have ho : hH.md.stateAt s₃.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) = hH.md.compressList hH.iv (xorPad k0 opad) 1 := by
    rw [hH.reloc s₂.mem s₃.mem (outer s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) i₃]
    exact Md.stateAt_of_repr hB0 hxl ((hH.repr _ _ _).1 rO₂)
  show bytesAt s'.mem (op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hm, m₅, e₄, ho, hH.md.blockAt_eq (by omega_using [hDL]) p₃, b₃, hmacBlockKey, ← dig,
    ← bytesAt_take _ _ hDN, hH.iterOk.link.hash_block hxl (bytesAt_length _ _ _)]

end

/-! ## Constant time -/

section

variable {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H.stream) sc s₀) (hp' : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H.stream) sc s₀')
  (hq : VG.Proof.Pbkdf2.Md.X86_64.Calls.PubEq s₀ s₀')

omit hH in
/-- The registers `oregs` agree in two runs. -/
theorem ko_agree (hq : VG.Proof.Pbkdf2.Md.X86_64.Calls.PubEq s₀ s₀') {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s ∧ s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀)
    (h' : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀' s' ∧ s'.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀') : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.oregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.1.rbx, h'.1.rbx, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, hq.rdi]
  · rw [h.2, h'.2, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, hq.rdi]
  · rw [h.1.r13, h'.1.r13, op, op, hq.rcx]
  · rw [h.1.r15, h'.1.r15, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr, hq.r8]
  · rw [h.1.rsp, h'.1.rsp, hq.rsp]

include hH hp hp' hq

theorem ct (hc : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.stream.finPrologue)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀ s ∧ s.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀' s' ∧ s'.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀' ∧ s'.gpr .rdx = s₀'.gpr .rdx) :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH.stream hp hp' hq (c := s₀.gpr .rdx)
    (F := fun s => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀ s ∧ s.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx)
    (F' := fun s => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀' s ∧ s.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀' ∧ s.gpr .rdx = s₀'.gpr .rdx) hc.fin1
    (fun _ _ h h' => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH.stream hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH.stream hp' k d x) fun _ ⟨k, a, si, m⟩ =>
      ⟨k, a, si.trans hq.rdx.symm, m⟩)
  have mid : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀ s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H.stream) s₀' s') (.block H.finMid)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s ∧ s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ ∧ s.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀' s' ∧ s'.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀') :=
    rel_taint VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kr_agree hq h h') hc.mid
      (fun s k => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.mid_ok hH hp k) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      (fun s k => WP.mono (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.mid_ok hH hp' k) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have cmp : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s ∧ s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀ ∧ s.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) ∧
        (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀' s' ∧ s'.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀' ∧ s'.gpr .rsi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀')) (compressAt H.compN H.compC)
      fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s ∧ s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) ∧ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀' s' ∧ s'.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀') :=
    rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, _, si⟩, ⟨k', _, si'⟩⟩ =>
        ⟨⟨_, _, _, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.callOk hH hp k si⟩, ⟨_, _, _, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.callOk hH hp' k' si'⟩,
          by rw [k.rbx, k'.rbx, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, hq.rdi], by rw [k.r15, k'.r15, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr, hq.r8],
          by rw [si, si', VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, hq.rdi], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun s ⟨k, bp, si⟩ => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cmp_ok hH hp k si fun s' k' bp' _ => ⟨k', bp'.trans bp⟩)
      (fun s ⟨k, bp, si⟩ => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cmp_ok hH hp' k si fun s' k' bp' _ => ⟨k', bp'.trans bp⟩)
  obtain ⟨_, hr⟩ := hc.out
  have out : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀ s ∧ s.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀) ∧ (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KO H s₀' s' ∧ s'.gpr .rbp = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.blk H s₀'))
      (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacFin.oregs) (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.ko_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (mid.seq (cmp.seq out)))

end

/-- HMAC's `finalize` is verified against `finG`, given the taint checks and
the facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Checks H) (hfit : H.stream.buf + H.stream.F ≤ 8 * sc)
    (hmx : H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.correct hH (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.pre_of hH.stream sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.ct hH (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.pre_of hH.stream sc h₁ hfit) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.pre_of hH.stream sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacFin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the functions, verified

What the kernel checks of a hash function's code does not depend on its
compression function or its streaming `init`, which our functions only call:
`core H` is `H` with both replaced by empty code, and the facts about every
instruction of `H`'s functions follow from those about `core H` and about the
two callees (`core_pbkdf2`, …). `CoreOK` is what the kernel checks of `core
H`, once for each hash function; `Callees` is what each implementation of the
compression function brings. From them, HMAC's `init` and `finalize`,
`iterate` and `pbkdf2` are verified against the shared contracts of
`Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)
open VG.Proof.Pbkdf2.X86_64 (iterK iterImp)

/-- No instruction of `c` writes `rsp`, from a check that runs in the kernel. -/
theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by
    have h' := List.all_eq_true.mp ((Code.allInstrs_eq _ c) ▸ h) i hi
    revert h'; cases Taint.clobbers i .rsp <;> simp

/-- `H` without the functions it calls: its own code. -/
def core (H : Hash) : Hash := ⟨H.P, H.D, H.W, "", .block [], "", .block [], "", "", "", "", ""⟩

/-! ## Every instruction, from the own code and the callees' -/

section
variable {H : Hash} {p : Instr → Bool} (hc : H.compC.allInstrs p = true) (hi : H.initC.allInstrs p = true)
include hc hi

theorem core_pbkdf2 (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).pbkdf2.allInstrs p = true) : H.pbkdf2.allInstrs p = true := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.initKeys, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream,
    Impl.Pbkdf2.Md.X86_64.Stream.callInit, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.allInstrs, hc, hi, Bool.and_true, Bool.true_and] at h ⊢
  exact h

theorem core_hmacInit (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).hmacInit.allInstrs p = true) : H.hmacInit.allInstrs p = true := by
  simp only [Hash.hmacInit, Hash.initKeys, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.allInstrs, hc, hi, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_hmacFin (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).hmacFin.allInstrs p = true) : H.hmacFin.allInstrs p = true := by
  simp only [Hash.hmacFin, Hash.finMid, Hash.finOut, Hash.finC, Hash.stream,
    Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_iterate (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).iterate.allInstrs p = true) : H.iterate.allInstrs p = true := by
  simp only [Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_updC (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).updC.allInstrs p = true) : H.updC.allInstrs p = true := by
  simp only [Hash.updC, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_finC (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).finC.allInstrs p = true) : H.finC.allInstrs p = true := by
  simp only [Hash.finC, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

end

/-! ## How deeply calls nest -/

section
variable {H : Hash} (hc : H.compC.depth = 0) (hi : H.initC.depth = 0)
include hc hi

theorem core_hmacInit_depth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).hmacInit.depth ≤ 2) : H.hmacInit.depth ≤ 2 := by
  simp only [Hash.hmacInit, Hash.initKeys, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.depth, hc, hi] at h ⊢
  exact h

omit hi in
theorem core_hmacFin_depth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).hmacFin.depth ≤ 2) : H.hmacFin.depth ≤ 2 := by
  simp only [Hash.hmacFin, Hash.finC, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_iterate_depth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).iterate.depth ≤ 2) : H.iterate.depth ≤ 2 := by
  simp only [Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_updC_depth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).updC.depth ≤ 1) : H.updC.depth ≤ 1 := by
  simp only [Hash.updC, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_finC_depth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).finC.depth ≤ 1) : H.finC.depth ≤ 1 := by
  simp only [Hash.finC, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, VG.Proof.Pbkdf2.Md.X86_64.core, Code.depth, hc] at h ⊢
  exact h

end

/-! ## How much stack HMAC and PBKDF2 use

HMAC's and PBKDF2's own code has no frames: the stack it uses is the return
addresses of the calls it nests, with callees that use none. -/

section
variable {H : Hash} (hc : H.compC.x86_64Depth = 0) (hi : H.initC.x86_64Depth = 0)
include hc hi

theorem core_hmacInit_xdepth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).hmacInit.x86_64Depth ≤ 16) : H.hmacInit.x86_64Depth ≤ 16 := by
  simp only [Hash.hmacInit, Hash.initKeys, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callInit,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.x86_64Depth, hc, hi] at h ⊢
  exact h

theorem core_pbkdf2_xdepth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).pbkdf2.x86_64Depth ≤ 24) : H.pbkdf2.x86_64Depth ≤ 24 := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.initKeys, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream,
    Impl.Pbkdf2.Md.X86_64.Stream.callInit, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.x86_64Depth, hc, hi] at h ⊢
  exact h

omit hi in
theorem core_hmacFin_xdepth (h : (VG.Proof.Pbkdf2.Md.X86_64.core H).hmacFin.x86_64Depth ≤ 16) : H.hmacFin.x86_64Depth ≤ 16 := by
  simp only [Hash.hmacFin, Hash.finC, Hash.stream, Impl.Pbkdf2.Md.X86_64.Stream.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    VG.Proof.Pbkdf2.Md.X86_64.core, Code.x86_64Depth, hc] at h ⊢
  exact h

end

/-! ## The taint checks, which look only at the own code -/

theorem HmacInit.Checks.of_core {H : Hash} (h : HmacInit.Checks (VG.Proof.Pbkdf2.Md.X86_64.core H)) : HmacInit.Checks H :=
  ⟨h.pro, h.argI, h.keys, h.mid, h.restore⟩

theorem HmacFin.Checks.of_core {H : Hash} (h : HmacFin.Checks (VG.Proof.Pbkdf2.Md.X86_64.core H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem Pbk.Checks.of_core {H : Hash} (h : Pbk.Checks (VG.Proof.Pbkdf2.Md.X86_64.core H)) : Pbk.Checks H :=
  ⟨h.load, h.entry, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.loopRegs, h.pieceA, h.finArgs,
    h.pieceC, h.tail, h.exit⟩

/-- What the kernel checks of a hash function's own code (`core H`), the
same for every implementation of its compression function: the taint checks
of the pieces between calls, that no instruction loads MXCSR or writes
`rsp`, and how deeply calls nest. -/
structure CoreOK (C : Hash) : Prop where
  pbk : Pbk.Checks C
  iter : VG.Proof.Pbkdf2.X86_64.Checks C.P C.D
  hinit : HmacInit.Checks C
  hfin : HmacFin.Checks C
  pbkMx : C.pbkdf2.allInstrs (fun i => !loadsMxcsr i) = true
  pbkSp : C.pbkdf2.allInstrs (fun i => !isa.writesSp i) = true
  hinitMx : C.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true
  hinitSp : C.hmacInit.allInstrs (fun i => !isa.writesSp i) = true
  hinitNs : C.hmacInit.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  hinitD : C.hmacInit.depth ≤ 2
  hfinMx : C.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true
  hfinSp : C.hmacFin.allInstrs (fun i => !isa.writesSp i) = true
  hfinNs : C.hmacFin.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  hfinD : C.hmacFin.depth ≤ 2
  /-- The stack HMAC's functions use, without that of their callees. -/
  hinitXD : C.hmacInit.x86_64Depth ≤ 16
  hfinXD : C.hmacFin.x86_64Depth ≤ 16
  /-- The stack `pbkdf2` uses, without that of its callees' callees. -/
  pbkXD : C.pbkdf2.x86_64Depth ≤ 24
  iterMx : C.iterate.allInstrs (fun i => !loadsMxcsr i) = true
  iterSp : C.iterate.allInstrs (fun i => !isa.writesSp i) = true
  iterNs : C.iterate.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  iterD : C.iterate.depth ≤ 2
  updMx : C.updC.allInstrs (fun i => !loadsMxcsr i) = true
  updNs : C.updC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  updD : C.updC.depth ≤ 1
  finMx : C.finC.allInstrs (fun i => !loadsMxcsr i) = true
  finNs : C.finC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  finD : C.finC.depth ≤ 1
  /-- HMAC's buffers fit in the working space. -/
  fitI : C.stream.buf ≤ 8 * C.W
  fitF : C.stream.buf + C.stream.F ≤ 8 * C.W

/-- What the kernel checks of the functions a hash function's code calls:
its compression function and its streaming `init`. -/
structure Callees (H : Hash) : Prop where
  cMx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true
  cSp : H.compC.allInstrs (fun i => !isa.writesSp i) = true
  cNs : H.compC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  cD : H.compC.depth = 0
  iMx : H.initC.allInstrs (fun i => !loadsMxcsr i) = true
  iSp : H.initC.allInstrs (fun i => !isa.writesSp i) = true
  iNs : H.initC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  iD : H.initC.depth = 0
  /-- Neither uses any stack. -/
  cXD : H.compC.x86_64Depth = 0
  iXD : H.initC.x86_64Depth = 0

namespace Callees

variable {H : Hash} (K : VG.Proof.Pbkdf2.Md.X86_64.Callees H) (C : VG.Proof.Pbkdf2.Md.X86_64.CoreOK (VG.Proof.Pbkdf2.Md.X86_64.core H))
include K C

theorem updMx : H.updC.allInstrs (fun i => !loadsMxcsr i) = true := VG.Proof.Pbkdf2.Md.X86_64.core_updC K.cMx C.updMx
theorem finMx : H.finC.allInstrs (fun i => !loadsMxcsr i) = true := VG.Proof.Pbkdf2.Md.X86_64.core_finC K.cMx C.finMx
theorem updSp : NoSp H.updC := VG.Proof.Pbkdf2.Md.X86_64.nosp_of (VG.Proof.Pbkdf2.Md.X86_64.core_updC K.cNs C.updNs)
theorem finSp : NoSp H.finC := VG.Proof.Pbkdf2.Md.X86_64.nosp_of (VG.Proof.Pbkdf2.Md.X86_64.core_finC K.cNs C.finNs)
theorem updD : H.updC.depth ≤ 1 := VG.Proof.Pbkdf2.Md.X86_64.core_updC_depth K.cD C.updD
theorem finD : H.finC.depth ≤ 1 := VG.Proof.Pbkdf2.Md.X86_64.core_finC_depth K.cD C.finD
theorem hmacInitXD : H.hmacInit.x86_64Depth ≤ 16 := VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit_xdepth K.cXD K.iXD C.hinitXD
theorem hmacFinXD : H.hmacFin.x86_64Depth ≤ 16 := VG.Proof.Pbkdf2.Md.X86_64.core_hmacFin_xdepth K.cXD C.hfinXD
theorem pbkdf2XD : H.pbkdf2.x86_64Depth ≤ 24 := VG.Proof.Pbkdf2.Md.X86_64.core_pbkdf2_xdepth K.cXD K.iXD C.pbkXD

end Callees

/-! ## The functions, verified -/

/-- A state satisfying `pbkdf2`'s precondition, with `8 sc` bytes of scratch
space: an empty password, salt and output, and `c = 1`; the stack arguments
(`out_len` and `scratch`) are zero, so `scratch` is at address 0. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x20000 | .r8 => 1 | .r9 => 0x30000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 16⟩]
  wr := [⟨0x30000, 0⟩, ⟨0, sc * 8⟩]

/-- A state satisfying the precondition of `pbkdf2` with its working space on
the stack: `pbkSat` without the working space, and with `out_len` its only
stack argument. -/
def pbkFrameSat : State :=
  { VG.Proof.Pbkdf2.Md.X86_64.pbkSat 0 with rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 8⟩], wr := [⟨0x30000, 0⟩] }

section
variable {H : Hash} (hH : HashOK H) (C : VG.Proof.Pbkdf2.Md.X86_64.CoreOK (VG.Proof.Pbkdf2.Md.X86_64.core H)) (K : VG.Proof.Pbkdf2.Md.X86_64.Callees H)
include hH C K

theorem hmacInit_ok (hsat : ∃ s, (Spec.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH H.W) :=
  HmacInit.verified hH (HmacInit.Checks.of_core C.hinit) C.fitI (VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit K.cMx K.iMx C.hinitMx)
    (initImp _ _ hsat).sat_left

theorem hmacFin_ok (hsat : ∃ s, (Spec.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (finG hH.SH H.W) :=
  HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) C.fitF (VG.Proof.Pbkdf2.Md.X86_64.core_hmacFin K.cMx C.hfinMx)
    (finImp _ _ hsat).sat_left

omit K in
theorem iterate_ok (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hmx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target H.iterate (iterK hH.SH H.W) :=
  VG.Proof.Pbkdf2.X86_64.verified hH.iterOk C.iter hH.comp (VG.Proof.Pbkdf2.Md.X86_64.core_iterate hmx C.iterMx) (iterImp _ _ hsat).sat_left

/-- HMAC's `init`, verified against the shared contract. -/
theorem hmacInit_verified (hsat : ∃ s, (Spec.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Spec.Hmac.initScratchContract hH.SH H.W X86_64.abi 16) :=
  (VG.Proof.Pbkdf2.Md.X86_64.hmacInit_ok hH C K hsat).of_implies (initImp _ _ hsat)

/-- HMAC's `finalize`, verified against the shared contract. -/
theorem hmacFin_verified (hsat : ∃ s, (Spec.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (Spec.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16) :=
  (VG.Proof.Pbkdf2.Md.X86_64.hmacFin_ok hH C K hsat).of_implies (finImp _ _ hsat)

/-- `iterate`, verified against the shared contract. -/
theorem iterate_verified (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8) :=
  (VG.Proof.Pbkdf2.Md.X86_64.iterate_ok hH C hsat K.cMx).of_implies (iterImp _ _ hsat)

/-- `pbkdf2`, verified against the shared contract. -/
theorem pbkdf2_verified
    (hsI : ∃ s, (Spec.Hmac.initScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Spec.Hmac.finalizeScratchContract hH.SH H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (Spec.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) X86_64.abi 24) :=
  (Pbk.verified hH hH.psizes (Pbk.Checks.of_core C.pbk)
    (VG.Proof.Pbkdf2.Md.X86_64.hmacInit_ok hH C K hsI) (VG.Proof.Pbkdf2.Md.X86_64.nosp_of (VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit K.cNs K.iNs C.hinitNs)) (VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit_depth K.cD K.iD C.hinitD)
    (VG.Proof.Pbkdf2.Md.X86_64.hmacFin_ok hH C K hsF) (VG.Proof.Pbkdf2.Md.X86_64.nosp_of (VG.Proof.Pbkdf2.Md.X86_64.core_hmacFin K.cNs C.hfinNs)) (VG.Proof.Pbkdf2.Md.X86_64.core_hmacFin_depth K.cD C.hfinD)
    (VG.Proof.Pbkdf2.Md.X86_64.iterate_ok hH C hsT K.cMx) (VG.Proof.Pbkdf2.Md.X86_64.nosp_of (VG.Proof.Pbkdf2.Md.X86_64.core_iterate K.cNs C.iterNs)) (VG.Proof.Pbkdf2.Md.X86_64.core_iterate_depth K.cD C.iterD)
    (VG.Proof.Pbkdf2.Md.X86_64.core_pbkdf2 K.cMx K.iMx C.pbkMx) (pbkImp _ _ hsat).sat_left).of_implies (pbkImp _ _ hsat)

omit hH in
theorem hmacInit_sp : H.hmacInit.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (VG.Proof.Pbkdf2.Md.X86_64.core_hmacInit K.cSp K.iSp C.hinitSp)

omit hH in
theorem hmacFin_sp : H.hmacFin.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (VG.Proof.Pbkdf2.Md.X86_64.core_hmacFin K.cSp C.hfinSp)

omit hH in
theorem iterate_sp : H.iterate.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (VG.Proof.Pbkdf2.Md.X86_64.core_iterate K.cSp C.iterSp)

omit hH in
theorem pbkdf2_sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (VG.Proof.Pbkdf2.Md.X86_64.core_pbkdf2 K.cSp K.iSp C.pbkSp)

end

end VG.Proof.Pbkdf2.Md.X86_64

end
