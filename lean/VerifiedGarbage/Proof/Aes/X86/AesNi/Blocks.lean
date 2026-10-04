import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop

/-!
# AES-NI on x86 (32-bit): encryption and decryption of whole blocks

The loops are proven once for any transformation `f` of a list of block
registers that computes `F` on each, given what it needs of the state
(`KP`, which the loops keep): `aes` and `aesDec`. After `c` blocks, the
first `c` data blocks hold `F` of the original ones (`Inv`); the six-block
and one-block bodies are the same code for different lists of registers
(`blocks_ok`). `encrypt_correct` and `decrypt_correct` add the prologue,
which saves `esi` and `edi` in the scratch buffer and loads the arguments,
the round keys through `aesimc` for decryption, and the epilogue.
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ aes aesDec regs6 loadData storeData blocks6 blocks1 blocksTail
  blocksPrologue blocksCmp blocksRestore imcKeys)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd
  addr_add part_contains part_sub_reg reg_contains in_reg)
open VG.X86.Wp (Upd Fupd wp_addi wp_subi wp_cmpi wp_test wp_ldm wp_stm toNat_ofNat_lt ofNat_beq_zero)

namespace Ecb

section
variable (s₀ : State)

/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := (bDatP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev orig (k : Nat) : Spec.Aes.State := Spec.Aes.stateAt s₀.mem (bAddr s₀ k)
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1))

end

/-- What a transformation of the block registers needs of the state is kept
by writing data blocks and moving `esi` and `edi`. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → (∀ r, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
    Frame [bDatR s₀] s.mem s'.mem → KP s'

/-- `f` computes `F` on each block register, for both lists of registers. -/
def BlkOk (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ rs, (rs = regs6 ∨ rs = [.xmm0]) → ∀ s, KP s →
    WP isa (f rs) s fun s' => (∀ b ∈ rs, st (s'.xmm b) = F (st (s.xmm b))) ∧ XFrame (.xmm6 :: rs) s s'

/-- After `c` blocks, with `esi` and `edi` at block `p`; the other registers
are `g`, and only the data has changed since `m₁`. -/
structure Inv (KP : State → Prop) (F : Spec.Aes.State → Spec.Aes.State) (s₀ : State) (g : Reg → BitVec 32)
    (m₁ : Mem) (c p : Nat) (s : State) : Prop where
  le : c ≤ bN s₀
  kp : KP s
  gpr : ∀ r, r ≠ .esi → r ≠ .edi → s.gpr r = g r
  esi : s.gpr .esi = bDatP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (bN s₀ - p)
  frame : Frame [bDatR s₀] m₁ s.mem
  blocks : ∀ k < bN s₀,
    Spec.Aes.stateAt s.mem (bAddr s₀ k) = if k < c then F (orig s₀ k) else orig s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) : rs.Nodup ∧ .xmm6 ∉ rs := by
  rcases h with rfl | rfl <;> decide

theorem regs_len (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) : 0 < rs.length ∧ rs.length ≤ 6 := by
  rcases h with rfl | rfl <;> decide

section Loops

variable {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
  {s₀ : State} {g : Reg → BitVec 32} {m₁ : Mem} (hp : BPre s₀) (hst : Stable KP s₀) (hf : BlkOk f F KP)
include hp hst hf

/-- The loads, `f` and the stores, for the blocks `c … c + N - 1` (`N` the
number of registers). -/
theorem blocks_ok (rs : List XReg) (hrs : rs = regs6 ∨ rs = [.xmm0]) (tail : List Instr)
    {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ bN s₀) {s : State} (hI : Inv KP F s₀ g m₁ c c s)
    (hQ : ∀ s', Inv KP F s₀ g m₁ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (loadData rs 0)) (.seq (f rs) (.block (storeData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
  have hw := hp.fD
  have hlen := (regs_len rs hrs).1
  have haddr : ∀ k, c + k < bN s₀ →
      addr (s.gpr .esi) (16 * (0 + k)) = bAddr s₀ (c + k) := fun k hk => by
    rw [hI.esi, addr_add, addr_eq (by omega), show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  have hout : ∀ k, c + k < bN s₀ → InRegions s.wr (bAddr s₀ (c + k)) 16 := fun k hk =>
    ⟨bDatR s₀, by rw [hI.wr, hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (loadData_ok rs 0 s hnd fun k hk => by
      rw [haddr k (by omega)]; exact in_rd (hout k (by omega))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf rs hrs s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₂.xmm rs[k]) = F (orig s₀ (c + k)) := fun k h => by
    rw [e₂ _ (List.getElem_mem h), e₁ k h, haddr k (by omega), hI.blocks _ (by omega)]
    simp only [show ¬ c + k < c by omega, ite_false]
  have hesi₂ : s₂.gpr .esi = s.gpr .esi := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok rs 0 s₂ (fun k hk => by
      rw [hesi₂, haddr k (by omega), f₂.wr, wr₁]; exact hout k (by omega))
      (by rw [hesi₂, hI.esi, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hesi₂, show 16 * 0 = 16 * (0 + 0) by rfl, haddr 0 (by omega), Nat.add_zero] at fr₃
  rw [hesi₂] at b₃
  have fr₃' : Frame [bDatR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨bDatR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by omega)⟩
  have g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  refine ⟨Nat.le_trans (by omega) hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
    (by rw [wr₃, f₂.wr, wr₁]) fr₃', fun r h1 h2 => by rw [g₃', hI.gpr r h1 h2],
    by rw [g₃', hI.esi], by rw [g₃', hI.edi], hI.frame.trans fr₃', ?_,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩
  intro k hk
  have out : ¬ (c ≤ k ∧ k < c + rs.length) →
      Spec.Aes.stateAt s₃.mem (bAddr s₀ k) = Spec.Aes.stateAt s.mem (bAddr s₀ k) :=
    fun hn => by
      rw [stateAt_eq, stateAt_eq]
      exact congrArg st <| fr₃.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  by_cases hlo : k < c
  · rw [out (by omega), hI.blocks k hk]
    simp only [hlo, show k < c + rs.length by omega, ite_true]
  · by_cases hhi : k < c + rs.length
    · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
      have hj : j < rs.length := by omega
      rw [← haddr j (by omega), b₃ j hj, ek j hj]
      simp only [hhi, ite_true]
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, hhi, ite_false]

omit hf in
/-- `add esi, 16 m; sub edi, m`, after `m` more blocks. -/
theorem advance_ok {rest : List Instr} {c m : Nat} (hc : c + m ≤ bN s₀) {s : State}
    (hI : Inv KP F s₀ g m₁ (c + m) c s) {Q : State → Prop}
    (hQ : ∀ s', Inv KP F s₀ g m₁ (c + m) (c + m) s' →
      s'.zf = some (decide (bN s₀ - (c + m) = 0)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * m))) :: .alu .sub .edi
      (.imm (BitVec.ofNat 32 m)) :: rest)) s Q := by
  have hw := hp.fD
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ hz => hQ s₂ ?_ ?_
  · have g₂ : ∀ r, r ≠ .esi → r ≠ .edi → s₂.gpr r = s.gpr r := fun r h1 h2 => by
      rw [u₂.other r h2, u₁.other r h1]
    refine ⟨hI.le, hst s s₂ hI.kp g₂ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _), fun r h1 h2 => by rw [g₂ r h1 h2, hI.gpr r h1 h2],
      ?_, ?_, by rw [u₂.mem, u₁.mem]; exact hI.frame, by rw [u₂.mem, u₁.mem]; exact hI.blocks,
      by rw [u₂.rd, u₁.rd, hI.rd], by rw [u₂.wr, u₁.wr, hI.wr]⟩
    · rw [u₂.other _ (by decide), u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    · rw [u₂.gpr, u₁.other _ (by decide), hI.edi]
      have : bN s₀ < 2 ^ 32 := by omega
      bv_omega
  · have hn : bN s₀ < 2 ^ 32 := by omega
    have e : BitVec.ofNat 32 (bN s₀ - c) - BitVec.ofNat 32 m = BitVec.ofNat 32 (bN s₀ - (c + m)) := by
      bv_omega
    rw [hz, u₁.other _ (by decide), hI.edi, e, ofNat_beq_zero (by omega)]

/-- The six-block body. -/
theorem body6_ok {c : Nat} (hc : c + 6 ≤ bN s₀) {s : State} (hI : Inv KP F s₀ g m₁ c c s) :
    WP isa (blocks6 f) s fun s' => Inv KP F s₀ g m₁ (c + 6) (c + 6) s' ∧
      s'.cf = some (decide (bN s₀ - (c + 6) < 6)) := by
  have hw := hp.fD
  refine blocks_ok hp hst hf regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  refine advance_ok hp hst (m := 6) hc hI₁ fun s₂ hI₂ _ => ?_
  refine wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ⟨?_, ?_⟩
  · exact { hI₂ with
      kp := hst _ _ hI₂.kp (fun r _ _ => by rw [u₃.gpr]) u₃.rd u₃.wr (by rw [u₃.mem]; exact Frame.refl _ _)
      gpr := fun r h1 h2 => by rw [u₃.gpr, hI₂.gpr r h1 h2]
      esi := by rw [u₃.gpr, hI₂.esi]
      edi := by rw [u₃.gpr, hI₂.edi]
      frame := by rw [u₃.mem]; exact hI₂.frame
      blocks := by rw [u₃.mem]; exact hI₂.blocks
      rd := by rw [u₃.rd, hI₂.rd]
      wr := by rw [u₃.wr, hI₂.wr] }
  · rw [hcf, hI₂.edi, toNat_ofNat_lt (by omega)]; rfl

/-- The one-block body. -/
theorem body1_ok {c : Nat} (hc : c < bN s₀) {s : State} (hI : Inv KP F s₀ g m₁ c c s) :
    WP isa (blocks1 f) s fun s' => Inv KP F s₀ g m₁ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (bN s₀ - (c + 1) = 0)) := by
  refine blocks_ok hp hst hf [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  exact advance_ok hp hst (m := 1) (rest := []) hc hI₁ fun s₂ hI₂ hz =>
    WP.block_nil ⟨hI₂, hz⟩

omit hf in
theorem test_ok {c : Nat} {s : State} (hI : Inv KP F s₀ g m₁ c c s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      Inv KP F s₀ g m₁ c c s' ∧ s'.zf = some (decide (bN s₀ - c = 0)) := by
  have hw := hp.fD
  refine wp_test fun s' u hz => WP.block_nil ⟨?_, ?_⟩
  · exact { hI with
      kp := hst _ _ hI.kp (fun r _ _ => by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)
      gpr := fun r h1 h2 => by rw [u.gpr, hI.gpr r h1 h2]
      esi := by rw [u.gpr, hI.esi]
      edi := by rw [u.gpr, hI.edi]
      frame := by rw [u.mem]; exact hI.frame
      blocks := by rw [u.mem]; exact hI.blocks
      rd := by rw [u.rd, hI.rd]
      wr := by rw [u.wr, hI.wr] }
  · rw [hz, hI.edi, BitVec.and_self, ofNat_beq_zero (by omega)]

/-- The blocks left after `c₀`, six and then one at a time. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : Inv KP F s₀ g m₁ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (bN s₀ - c₀ < 6))) :
    WP isa (blocksTail f) s₁ (Inv KP F s₀ g m₁ (bN s₀) (bN s₀)) := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, bN s₀ - c < 6 ∧ Inv KP F s₀ g m₁ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (bN s₀ - c₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = bN s₀ - c ∧ c + 6 ≤ bN s₀ ∧ Inv KP F s₀ g m₁ c c s
      have hstep : ∀ m s, I6 m s → WP isa (blocks6 f) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, bN s₀ - c < 6 ∧ Inv KP F s₀ g m₁ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body6_ok hp hst hf hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : bN s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], bN s₀ - (c + 6), by omega, c + 6, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I6 hstep (bN s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hst hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (bN s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = bN s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = bN s₀ - c ∧ c < bN s₀ ∧ Inv KP F s₀ g m₁ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blocks1 f) s (fun s' =>
        (eval .ne s' = some false ∧ Inv KP F s₀ g m₁ (bN s₀) (bN s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hst hf hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : bN s₀ - (c + 1) = 0
      · have : c + 1 = bN s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], bN s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < bN s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (bN s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

end Loops

end Ecb

end VG.Proof.Aes.X86.AesNi
