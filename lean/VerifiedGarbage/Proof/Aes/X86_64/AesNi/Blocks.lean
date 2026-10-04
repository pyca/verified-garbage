import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
import VerifiedGarbage.Proof.Aes.X86_64.Blocks

/-!
# AES-NI: encryption and decryption of whole blocks

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86_64.AesNi.encryptBlocks` and `decryptBlocks` against the
contracts of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, through
the per-target contract of the bitsliced implementation
(`Proof.Aes.blocksX86_64`). The loops are proven once for any
transformation `f` of a list of block registers that computes `F` on each,
given what it needs of the state (`KP`, which the loops keep): `aes` and
`aesDec`. After `c` blocks, the first `c` data blocks hold `F` of the
original ones (`Inv`); the eight-block and one-block bodies are the same
code for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ aes aesDec regs8 loadData storeData blocksLoad blocks8 blocks1
  blocksTail imcKeys)
open VG.Spec.Aes (bytesAt)

/-! ## Blocks as states -/

theorem stateAt_eq (m : Mem) (a : Addr) : Spec.Aes.stateAt m a = st (m.readW a 128) :=
  st_ext fun i hi => by
    rw [getD_st _ hi, VG.Proof.Gcm.X86_64.byte_readW _ _ hi]
    simp [Spec.Aes.stateAt, Vector.getD, hi]

/-- Load the block at `rdx + d` into `b`. -/
theorem load1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad b (at_ .rdx d)]) s fun s' =>
      s'.xmm b = s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.setXmm,
    State.load128, ea_at, hin, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, trivial, trivial, trivial, trivial, fun r h => by simp [h]⟩

/-- Store `b` to the block at `rdx + d`. -/
theorem store1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquStore (at_ .rdx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) (s.xmm b) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, ea_at,
    hin, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun _ => trivial⟩

theorem loadData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) :
    WP isa (.block (loadData regs j)) s fun s' =>
      (∀ k (h : k < regs.length),
        st (s'.xmm regs[k]) = Spec.Aes.stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (load1_ok b (16 * j) s hin0) fun s₁ ⟨x₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, x₁, stateAt_eq, ofInt_natCast]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, o₁ r hr.1]

theorem storeData_ok (regs : List XReg) (j : Nat) (s : State)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr .rdx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (storeData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), Spec.Aes.stateAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
        st (s.xmm regs[k])) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hw
    rw [storeData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (store1_ok b (16 * j) s hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    rw [ofInt_natCast] at m₁
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r => (hx r).trans (x₁ r)⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [stateAt_eq, hf.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            intro a h₁ h₂
            simp only [Region.Contains] at h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr .rdx).isLt
            omega) (by decide), m₁, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega, hb k (by simpa using hk), x₁]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega

/-! ## The loops, for any transformation of the blocks -/

namespace Ecb

section
variable (s₀ : State)

abbrev sp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev sR : Region := ⟨sp s₀, 240⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨s₀.gpr .r8, 2048⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (sp s₀) (16 * (nr s₀ + 1))
/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev orig (k : Nat) : Spec.Aes.State := Spec.Aes.stateAt s₀.mem (bAddr s₀ k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [sR s₀]
  wr : s₀.wr = [dR s₀, scrR s₀]
  s_d : (sR s₀).Disjoint (dR s₀)
  s_scr : (sR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  wrap : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14

theorem pre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} (s₀ : State)
    (h : (Proof.Aes.blocksX86_64 f).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem nb_lt : 16 * nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

theorem in_blk {k : Nat} (hk : k < nb s₀) : (dR s₀).Contains (bAddr s₀ k) 16 :=
  contains_offset (by omega) (by have := hp.wrap; omega)

end Pre

/-- What a transformation of the block registers needs of the state is kept
by writing data blocks and moving `rdx` and `rcx`. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
    Frame [dR s₀] s.mem s'.mem → KP s'

/-- `f` computes `F` on each block register, for both lists of registers. -/
def BlkOk (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ rs, (rs = regs8 ∨ rs = [.xmm0]) → ∀ s, KP s →
    WP isa (f rs) s fun s' => (∀ b ∈ rs, st (s'.xmm b) = F (st (s.xmm b))) ∧ XFrame (.xmm8 :: rs) s s'

/-- After `c` blocks, with `rdx` and `rcx` at block `p`. -/
structure Inv (KP : State → Prop) (F : Spec.Aes.State → Spec.Aes.State) (s₀ : State) (c p : Nat)
    (s : State) : Prop where
  le : c ≤ nb s₀
  kp : KP s
  gpr : ∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .r10 → s.gpr r = s₀.gpr r
  r10 : s.gpr .r10 = sp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  rdx : s.gpr .rdx = bAddr s₀ p
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - p)
  frame : Frame [dR s₀, scrR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀,
    Spec.Aes.stateAt s.mem (bAddr s₀ k) = if k < c then F (orig s₀ k) else orig s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : rs = regs8 ∨ rs = [.xmm0]) : rs.Nodup ∧ .xmm8 ∉ rs := by
  rcases h with rfl | rfl <;> decide

theorem run_in {d a : Addr} {nb c n : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hc : c + n ≤ nb)
    (ha : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : (a - d).toNat < 16 * nb := by
  rw [off_toNat _ _ (by omega)] at ha
  have := (a - d).isLt
  omega

theorem run_sep {d a : Addr} {nb c n k : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hk : k < nb)
    (hc : c + n ≤ nb) (hn : ¬ (c ≤ k ∧ k < c + n))
    (h₁ : (a - (d + BitVec.ofNat 64 (16 * k))).toNat < 16)
    (h₂ : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : False := by
  rw [off_toNat _ _ (by omega)] at h₁ h₂
  have := (a - d).isLt
  omega

theorem beq_ofNat_zero' {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

section Loops

variable {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
  {s₀ : State} (hp : Pre s₀) (hst : Stable KP s₀) (hf : BlkOk f F KP)
include hp hst hf

/-- The loads, `f` and the stores, for the blocks `c … c + N - 1` (`N` the
number of registers). -/
theorem blocks_ok (rs : List XReg) (hrs : rs = regs8 ∨ rs = [.xmm0]) (tail : List Instr)
    {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ nb s₀) {s : State} (hI : Inv KP F s₀ c c s)
    (hQ : ∀ s', Inv KP F s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (loadData rs 0)) (.seq (f rs) (.block (storeData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h8⟩ := regs_nodup rs hrs
  have hlen : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.wrap
  have hrdxN : (s.gpr .rdx).toNat = (dp s₀).toNat + 16 * c := by
    rw [hI.rdx, bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have addr : ∀ (t : State), t.gpr .rdx = s.gpr .rdx → ∀ k,
      t.gpr .rdx + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int) = bAddr s₀ (c + k) :=
    fun t ht k => by
      rw [ht, hI.rdx, ofInt_natCast, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  have addr' : ∀ k, s.gpr .rdx + BitVec.ofNat 64 (16 * (0 + k)) = bAddr s₀ (c + k) :=
    fun k => by rw [← addr s rfl, ofInt_natCast]
  have hout : ∀ k, c + k < nb s₀ → InRegions s.wr (bAddr s₀ (c + k)) 16 := fun k hk =>
    ⟨dR s₀, by simp [hI.wr, hp.wr], hp.in_blk hk⟩
  refine WP.seq (WP.mono (loadData_ok rs 0 s hnd fun k hk => by
      rw [addr s rfl]; obtain ⟨r, hr, h⟩ := hout k (by omega)
      exact ⟨r, List.mem_append_right _ hr, h⟩) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  simp only [addr'] at e₁
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf rs hrs s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₂.xmm rs[k]) = F (orig s₀ (c + k)) := fun k h => by
    rw [e₂ _ (List.getElem_mem h), e₁ k h, hI.blocks _ (by omega)]
    simp only [show ¬ c + k < c by omega, ite_false]
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok rs 0 s₂ (fun k hk => by
      rw [addr s₂ hrdx₂, f₂.wr, wr₁]; exact hout k (by omega)) (by rw [hrdx₂, hrdxN]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hrdx₂] at fr₃
  rw [hrdx₂] at b₃
  rw [Nat.mul_zero, BitVec.add_zero, hI.rdx] at fr₃
  simp only [addr'] at b₃
  have fr₃' : Frame [dR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      exact run_in hw hc ha⟩
  have g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  refine ⟨Nat.le_trans (by omega) hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
    (by rw [wr₃, f₂.wr, wr₁]) fr₃', fun r h1 h2 h3 => by rw [g₃', hI.gpr r h1 h2 h3],
    by rw [g₃', hI.r10], by rw [g₃', hI.rdx], by rw [g₃', hI.rcx],
    hI.frame.trans (fr₃'.mono fun r hr => by simp at hr; simp [hr]), ?_,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩
  intro k hk
  have out : ¬ (c ≤ k ∧ k < c + rs.length) →
      Spec.Aes.stateAt s₃.mem (bAddr s₀ k) = Spec.Aes.stateAt s.mem (bAddr s₀ k) :=
    fun hn => by
      rw [stateAt_eq, stateAt_eq]
      exact congrArg st <| fr₃.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        simp only [Region.Contains, bAddr] at h₁ h₂
        exact run_sep (a := a) hw hk hc hn (by omega) (by omega)) (by decide)
  by_cases hlo : k < c
  · rw [out (by omega), hI.blocks k hk]
    simp only [hlo, show k < c + rs.length by omega, ite_true]
  · by_cases hhi : k < c + rs.length
    · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
      have hj : j < rs.length := by omega
      rw [b₃ j hj, ek j hj]
      simp only [hhi, ite_true]
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, hhi, ite_false]

/-- The eight-block body. -/
theorem body8_ok {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State} (hI : Inv KP F s₀ c c s) :
    WP isa (blocks8 f) s fun s' => Inv KP F s₀ (c + 8) (c + 8) s' ∧
      s'.cf = some (decide (nb s₀ - (c + 8) < 8)) := by
  have hn := hp.nb_lt
  refine blocks_ok hp hst hf regs8 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e128, e8, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 8 = BitVec.ofNat 64 (nb s₀ - (c + 8)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    kp := hst _ _ hI₁.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₁.gpr r h1 h2 h3]
    r10 := by simp [hI₁.r10]
    rdx := by simp (config := {decide := true}) only [bAddr, ite_false, ite_true]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - (c + 8) < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {c : Nat} (hc : c < nb s₀) {s : State} (hI : Inv KP F s₀ c c s) :
    WP isa (blocks1 f) s fun s' => Inv KP F s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (nb s₀ - (c + 1) = 0)) := by
  have hn := hp.nb_lt
  refine blocks_ok hp hst hf [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_false, e16, e1, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 1 = BitVec.ofNat 64 (nb s₀ - (c + 1)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    kp := hst _ _ hI₁.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₁.gpr r h1 h2 h3]
    r10 := by simp [hI₁.r10]
    rdx := by simp (config := {decide := true}) only [bAddr, ite_false, ite_true]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  rw [hsub, beq_ofNat_zero' (by omega)]

omit hf in
theorem test_ok {c : Nat} {s : State} (hI : Inv KP F s₀ c c s) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun s' =>
      Inv KP F s₀ c c s' ∧ s'.zf = some (decide (nb s₀ - c = 0)) := by
  have hn := hp.nb_lt
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with kp := hst _ _ hI.kp (fun _ _ _ => rfl) rfl rfl (Frame.refl _ _) },
    by rw [beq_ofNat_zero' (by omega)]⟩

/-- The blocks left after `c`, eight and then one at a time. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : Inv KP F s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (nb s₀ - c₀ < 8))) :
    WP isa (blocksTail f) s₁ (Inv KP F s₀ (nb s₀) (nb s₀)) := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 8 ∧ Inv KP F s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ - c₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 8 ≤ nb s₀ ∧ Inv KP F s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (blocks8 f) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, nb s₀ - c < 8 ∧ Inv KP F s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body8_ok hp hst hf hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (nb s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hst hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (nb s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c < nb s₀ ∧ Inv KP F s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blocks1 f) s (fun s' =>
        (eval .ne s' = some false ∧ Inv KP F s₀ (nb s₀) (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hst hf hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nb s₀ - (c + 1) = 0
      · have : c + 1 = nb s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (nb s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

end Loops

/-! ## The prologue, the epilogue and the two functions -/

theorem blocksLoad_ok (s : State) :
    WP isa (.block blocksLoad) s fun s' =>
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, s'.xmm r = s.xmm r) ∧ s'.cf = some (decide ((s.gpr .rcx).toNat < 8)) := by
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksLoad, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e8,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by bv_omega, fun r h => by simp [h], trivial, trivial, trivial, fun _ => trivial, ?_⟩
  simp

/-- `Keys` reads only the key schedule, the regions and `rdi`. -/
theorem keys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : Keys nr w s)
    (hrdi : s'.gpr .rdi = s.gpr .rdi) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hm : bytesAt s'.mem (s.gpr .rdi) (16 * (nr + 1)) = bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1))) :
    Keys nr w s' :=
  ⟨by rw [hrdi, hm]; exact h.sched, h.le, by rw [hrd, hwr, hrdi]; exact h.keys⟩

theorem dkeys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : DKeys nr w s)
    (hrdi : s'.gpr .rdi = s.gpr .rdi) (hr8 : s'.gpr .r8 = s.gpr .r8) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr)
    (hm : bytesAt s'.mem (s.gpr .rdi) (16 * (nr + 1)) = bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1)))
    (hm' : ∀ j, 1 ≤ j → j < nr →
      s'.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128 =
        s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) :
    DKeys nr w s' :=
  ⟨keys_congr h.keys hrdi hrd hwr hm, fun j h1 h2 => by
    rw [hrd, hwr, hr8, hm' j h1 h2]; exact h.imc j h1 h2⟩

/-- What encryption needs, from `s₀`. -/
def KPe (s₀ : State) (s : State) : Prop :=
  Keys (nr s₀) (sch s₀) s ∧ s.gpr .rdi = sp s₀ ∧ s.gpr .rsi = s₀.gpr .rsi ∧
    s.gpr .r10 = sp s₀ + BitVec.ofNat 64 (16 * nr s₀)

/-- What decryption needs, from `s₀`. -/
def KPd (s₀ : State) (s : State) : Prop :=
  DKeys (nr s₀) (sch s₀) s ∧ s.gpr .rdi = sp s₀ ∧ s.gpr .r8 = s₀.gpr .r8 ∧ s.gpr .rsi = s₀.gpr .rsi ∧
    s.gpr .r10 = sp s₀ + BitVec.ofNat 64 (16 * nr s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem sch_congr {m m' : Mem} (hf : Frame [dR s₀] m m') :
    bytesAt m' (sp s₀) (16 * (nr s₀ + 1)) = bytesAt m (sp s₀) (16 * (nr s₀ + 1)) := by
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨sp s₀, 16 * (nr s₀ + 1)⟩) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.s_d.sub_left (Region.sub_prefix hn)) (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi

theorem kpe_stable : Stable (KPe s₀) s₀ := fun s s' ⟨hK, hrdi, hrsi, hr10⟩ hg hrd hwr hf => by
  have g := fun r h1 h2 => hg r h1 h2
  refine ⟨keys_congr hK (g _ (by decide) (by decide)) hrd hwr (by rw [hrdi]; exact sch_congr hp hf),
    by rw [g _ (by decide) (by decide), hrdi], by rw [g _ (by decide) (by decide), hrsi],
    by rw [g _ (by decide) (by decide), hr10]⟩

theorem kpd_stable : Stable (KPd s₀) s₀ := fun s s' ⟨hK, hrdi, hr8, hrsi, hr10⟩ hg hrd hwr hf => by
  have g := fun r h1 h2 => hg r h1 h2
  refine ⟨dkeys_congr hK (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) hrd hwr
      (by rw [hrdi]; exact sch_congr hp hf) fun j h1 h2 => ?_,
    by rw [g _ (by decide) (by decide), hrdi], by rw [g _ (by decide) (by decide), hr8],
    by rw [g _ (by decide) (by decide), hrsi], by rw [g _ (by decide) (by decide), hr10]⟩
  have hj : j ≤ 13 := by rcases hp.rounds with h | h | h <;> omega
  rw [hr8, ofInt_natCast]
  exact hf.readW (r := ⟨s₀.gpr .r8 + BitVec.ofNat 64 (16 * j), 16⟩) (w := 128) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.d_scr.sub_right (Offset.sub_base _ (by omega))).symm) (by decide)

theorem aes_blkOk : BlkOk aes (Spec.Aes.cipher (nr s₀) (sch s₀)) (KPe s₀) :=
  fun rs hrs s ⟨hK, hrdi, hrsi, hr10⟩ => by
    obtain ⟨hnd, h8⟩ := regs_nodup rs hrs
    exact aes_ok rs hnd h8 hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

theorem aesDec_blkOk : BlkOk aesDec (Spec.Aes.invCipher (nr s₀) (sch s₀)) (KPd s₀) :=
  fun rs hrs s ⟨hK, hrdi, _, hrsi, hr10⟩ => by
    obtain ⟨hnd, h8⟩ := regs_nodup rs hrs
    exact aesDec_ok rs hnd h8 hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

/-- From the state after the loops, the postcondition. -/
theorem post_of {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s : State} (hI : Inv KP (F (nr s₀) (sch s₀)) s₀ (nb s₀) (nb s₀) s) :
    gprPreserved s₀ s ∧ (Proof.Aes.blocksX86_64 F).post s₀ s := by
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · refine hI.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_d
    · exact hp.ret_scr
  · show Spec.Aes.statesAt s.mem (dp s₀) (nb s₀) = _
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk := List.mem_range.mp hk
    have := hI.blocks k hk
    simp only [hk, ite_true] at this
    exact this

end

/-- The keys and the regions at the start, for `KPe`. -/
theorem keys₀ {s₀ : State} (hp : Pre s₀) : Keys (nr s₀) (sch s₀) s₀ :=
  ⟨rfl, by rcases hp.rounds with h | h | h <;> omega, fun j hj => ⟨sR s₀, by simp [hp.rd], by
    rw [ofInt_natCast]; exact contains_offset (by rcases hp.rounds with h | h | h <;> omega)
      (by rcases hp.rounds with h | h | h <;> omega)⟩⟩

theorem encrypt_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Aes.X86_64.AesNi.encryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s₀ s' := by
  refine WP.seq (WP.mono (blocksLoad_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁, _, cf₁⟩ => ?_)
  have hI₁ : Inv (KPe s₀) (Spec.Aes.cipher (nr s₀) (sch s₀)) s₀ 0 0 s₁ :=
    { le := Nat.zero_le _
      kp := ⟨keys_congr (keys₀ hp) (g₁ _ (by decide)) rd₁ wr₁ (by rw [m₁]), g₁ _ (by decide),
        g₁ _ (by decide), r10₁⟩
      gpr := fun r _ _ h3 => g₁ r h3
      r10 := r10₁
      rdx := by rw [g₁ _ (by decide)]; simp [bAddr]
      rcx := by rw [g₁ _ (by decide)]; simp [nb]
      frame := by rw [m₁]; exact Frame.refl _ _
      blocks := fun k _ => by simp [m₁]
      rd := rd₁
      wr := wr₁ }
  exact WP.mono (tail_ok hp (kpe_stable hp) (aes_blkOk hp) hI₁ (by simpa using cf₁)) fun s hI =>
    post_of hp hI

theorem decrypt_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Aes.X86_64.AesNi.decryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s₀ s' := by
  have hscr : (scrR s₀) ∈ s₀.wr := by rw [hp.wr]; simp
  have hsch : (sR s₀) ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by rw [hp.rd]; simp)
  refine WP.seq (WP.mono (imcKeys_ok hp.rounds (by simp) hscr hsch hp.s_scr)
    fun s₁ ⟨S, hS₁, hcov⟩ => ?_)
  have hK₁ := dKeys_of_imc (keys₀ hp) hscr hp.s_scr hS₁ hcov
  refine WP.seq (WP.mono (blocksLoad_ok s₁) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, _, cf₂⟩ => ?_)
  have g : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂ r h, hS₁.gpr]
  have hI₂ : Inv (KPd s₀) (Spec.Aes.invCipher (nr s₀) (sch s₀)) s₀ 0 0 s₂ :=
    { le := Nat.zero_le _
      kp := ⟨dkeys_congr hK₁ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ (by rw [m₂])
          (fun _ _ _ => by rw [m₂]), g _ (by decide), g _ (by decide), g _ (by decide),
        by rw [r10₂, hS₁.gpr]⟩
      gpr := fun r _ _ h3 => g r h3
      r10 := by rw [r10₂, hS₁.gpr]
      rdx := by rw [g _ (by decide)]; simp [bAddr]
      rcx := by rw [g _ (by decide)]; simp [nb]
      frame := by
        rw [m₂]
        exact hS₁.frame.mono fun r hr => by simp at hr; simp [hr]
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, orig]
        rw [m₂, stateAt_eq, stateAt_eq]
        exact congrArg st <| hS₁.frame.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128)
          (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.d_scr.sub_left (Offset.sub_base _ (by omega))) (by decide)
      rd := by rw [rd₂, hS₁.rd]
      wr := by rw [wr₂, hS₁.wr] }
  have hcf : s₂.cf = some (decide (nb s₀ - 0 < 8)) := by
    rw [cf₂, hS₁.gpr]; simp [nb]
  exact WP.mono (tail_ok hp (kpd_stable hp) (aesDec_blkOk hp) hI₂ hcf) fun s hI => post_of hp hI

end Ecb

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.encrypt_correct (Ecb.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.decrypt_correct (Ecb.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.AesNi.encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub Impl.Aes.X86_64.AesNi.decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.encryptBlocks (Spec.Aes.encryptBlocksContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat)

theorem decryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.decryptBlocks (Spec.Aes.decryptBlocksContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat)

end VG.Proof.Aes.X86_64.AesNi
