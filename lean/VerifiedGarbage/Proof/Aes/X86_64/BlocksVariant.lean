module

public import VerifiedGarbage.Proof.Framework.X86_64.CalleeSide
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Spec.AesEcb.Contract
public import VerifiedGarbage.Impl.AesCfb8.X86_64
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Impl.AesCfb.X86_64
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Impl.AesOfb.X86_64
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Impl.AesOcb.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Aes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks
meta import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
meta import VerifiedGarbage.Proof.Framework.X86_64.YFrame
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
public import VerifiedGarbage.Proof.Aes.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
meta import VerifiedGarbage.Proof.Aes.X86_64.Blocks
meta import VerifiedGarbage.Proof.Aes.Rounds
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Aes.X86_64.VaesBlocks.Blocks`, which this module and modules that import it used -/

section

/-! ### `Aes.X86_64.AesNi.Blocks`, which this module and modules that import it used -/

section

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

@[expose] public section

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
    have hin0 := hin 0 (by omega_arith)
    rw [Nat.add_zero] at hin0
    refine WP.mono (load1_ok b (16 * j) s hin0) fun s₁ ⟨x₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact hin (k + 1) (by omega_arith)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, x₁, stateAt_eq, ofInt_natCast]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega_arith]
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
    have hin0 := hin 0 (by omega_arith)
    rw [Nat.add_zero] at hin0
    refine WP.mono (store1_ok b (16 * j) s hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega_arith]; exact hin (k + 1) (by omega_arith))
      (by rw [hrdx]; omega_arith)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    rw [AesNi.ofInt_natCast] at m₁
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r => (hx r).trans (x₁ r)⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [stateAt_eq, hf.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            intro a h₁ h₂
            simp only [Region.Contains] at h₁ h₂
            rw [off_toNat _ _ (by omega_arith)] at h₁ h₂
            have := (a - s.gpr .rdx).isLt
            omega_arith) (by decide), m₁, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega_arith, hb k (by simpa using hk), x₁]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega_arith)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega_arith

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

/-- What the loops need: the data, and then the scratch buffer if any, which
only decryption touches (`PreS`). -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [sR s₀]
  wr : ∃ X, s₀.wr = dR s₀ :: X
  s_d : (sR s₀).Disjoint (dR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  wrap : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14

/-- What decryption needs of the scratch buffer, where it keeps its key schedule. -/
structure PreS (s₀ : State) : Prop where
  wr : s₀.wr = [dR s₀, scrR s₀]
  s_scr : (sR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} (s₀ : State)
    (h : (Proof.Aes.blocksX86_64 f).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, _, _, h6, _, h8, h9⟩ := h
  exact ⟨h1, ⟨_, h2⟩, h3, h6, h8, h9⟩

theorem preS_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} (s₀ : State)
    (h : (Proof.Aes.blocksX86_64 f).pre s₀) : PreS s₀ := by
  obtain ⟨_, h2, _, h4, h5, _, h7, _, _⟩ := h
  exact ⟨h2, h4, h5, h7⟩

theorem preF_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} (s₀ : State)
    (h : (Proof.Aes.blocksX86_64F f).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h6, h8, h9⟩ := h
  exact ⟨h1, ⟨_, h2⟩, h3, h6, h8, h9⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem nb_lt : 16 * nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega_arith

theorem in_blk {k : Nat} (hk : k < nb s₀) : (dR s₀).Contains (bAddr s₀ k) 16 :=
  contains_offset (by omega_arith) (by have := hp.wrap; omega_arith)

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
  rw [off_toNat _ _ (by omega_arith)] at ha
  have := (a - d).isLt
  omega_arith

theorem run_sep {d a : Addr} {nb c n k : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hk : k < nb)
    (hc : c + n ≤ nb) (hn : ¬ (c ≤ k ∧ k < c + n))
    (h₁ : (a - (d + BitVec.ofNat 64 (16 * k))).toNat < 16)
    (h₂ : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : False := by
  rw [off_toNat _ _ (by omega_arith)] at h₁ h₂
  have := (a - d).isLt
  omega_arith

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
    rw [hI.rdx, bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  have addr : ∀ (t : State), t.gpr .rdx = s.gpr .rdx → ∀ k,
      t.gpr .rdx + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int) = bAddr s₀ (c + k) :=
    fun t ht k => by
      rw [ht, hI.rdx, ofInt_natCast, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_arith]
  have addr' : ∀ k, s.gpr .rdx + BitVec.ofNat 64 (16 * (0 + k)) = bAddr s₀ (c + k) :=
    fun k => by rw [← addr s rfl, ofInt_natCast]
  have hout : ∀ k, c + k < nb s₀ → InRegions s.wr (bAddr s₀ (c + k)) 16 := fun k hk =>
    ⟨dR s₀, by obtain ⟨_, hw⟩ := hp.wr; simp [hI.wr, hw], hp.in_blk hk⟩
  refine WP.seq (WP.mono (loadData_ok rs 0 s hnd fun k hk => by
      rw [addr s rfl]; obtain ⟨r, hr, h⟩ := hout k (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, h⟩) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  simp only [addr'] at e₁
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf rs hrs s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₂.xmm rs[k]) = F (orig s₀ (c + k)) := fun k h => by
    rw [e₂ _ (List.getElem_mem h), e₁ k h, hI.blocks _ (by omega_arith)]
    simp only [show ¬ c + k < c by omega_arith, ite_false]
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok rs 0 s₂ (fun k hk => by
      rw [addr s₂ hrdx₂, f₂.wr, wr₁]; exact hout k (by omega_arith)) (by rw [hrdx₂, hrdxN]; omega_arith))
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
  refine ⟨Nat.le_trans (by omega_arith) hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
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
        exact run_sep (a := a) hw hk hc hn (by omega_arith) (by omega_arith)) (by decide)
  by_cases hlo : k < c
  · rw [out (by omega_arith), hI.blocks k hk]
    simp only [hlo, show k < c + rs.length by omega_arith, ite_true]
  · by_cases hhi : k < c + rs.length
    · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega_arith⟩
      have hj : j < rs.length := by omega_arith
      rw [b₃ j hj, ek j hj]
      simp only [hhi, ite_true]
    · rw [out (by omega_arith), hI.blocks k hk]
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
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 8 = BitVec.ofNat 64 (nb s₀ - (c + 8)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    kp := hst _ _ hI₁.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₁.gpr r h1 h2 h3]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, bAddr]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - (c + 8) < 2 ^ 64 by omega_arith),
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
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 1 = BitVec.ofNat 64 (nb s₀ - (c + 1)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    kp := hst _ _ hI₁.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₁.gpr r h1 h2 h3]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, bAddr]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  rw [hsub, beq_ofNat_zero' (by omega_arith)]

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
    by rw [beq_ofNat_zero' (by omega_arith)]⟩

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
        · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 8), by omega_arith, c + 8, rfl, by omega_arith, hI'⟩
      exact WP.loop (M := isa) I8 hstep (nb s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_arith, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hst hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (nb s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nb s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c < nb s₀ ∧ Inv KP F s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blocks1 f) s (fun s' =>
        (eval .ne s' = some false ∧ Inv KP F s₀ (nb s₀) (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hst hf hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nb s₀ - (c + 1) = 0
      · have : c + 1 = nb s₀ := by omega_arith
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nb s₀ - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
    have hlt : c < nb s₀ := by have := hI₃.le; simp at h; omega_arith
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
  simp only [reduceCtorEq, ↓reduceIte, blocksLoad, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, e8,
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
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨sp s₀, 16 * (nr s₀ + 1)⟩) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.s_d.sub_left (Region.sub_prefix hn)) (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega_arith) hi

theorem kpe_stable : Stable (KPe s₀) s₀ := fun s s' ⟨hK, hrdi, hrsi, hr10⟩ hg hrd hwr hf => by
  have g := fun r h1 h2 => hg r h1 h2
  refine ⟨keys_congr hK (g _ (by decide) (by decide)) hrd hwr (by rw [hrdi]; exact sch_congr hp hf),
    by rw [g _ (by decide) (by decide), hrdi], by rw [g _ (by decide) (by decide), hrsi],
    by rw [g _ (by decide) (by decide), hr10]⟩

theorem kpd_stable (hs : PreS s₀) : Stable (KPd s₀) s₀ := fun s s' ⟨hK, hrdi, hr8, hrsi, hr10⟩ hg hrd hwr hf => by
  have g := fun r h1 h2 => hg r h1 h2
  refine ⟨dkeys_congr hK (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) hrd hwr
      (by rw [hrdi]; exact sch_congr hp hf) fun j h1 h2 => ?_,
    by rw [g _ (by decide) (by decide), hrdi], by rw [g _ (by decide) (by decide), hr8],
    by rw [g _ (by decide) (by decide), hrsi], by rw [g _ (by decide) (by decide), hr10]⟩
  have hj : j ≤ 13 := by rcases hp.rounds with h | h | h <;> omega_arith
  rw [hr8, ofInt_natCast]
  exact hf.readW (r := ⟨s₀.gpr .r8 + BitVec.ofNat 64 (16 * j), 16⟩) (w := 128) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hs.d_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm) (by decide)

theorem aes_blkOk : BlkOk aes (Spec.Aes.cipher (nr s₀) (sch s₀)) (KPe s₀) :=
  fun rs hrs s ⟨hK, hrdi, hrsi, hr10⟩ => by
    obtain ⟨hnd, h8⟩ := regs_nodup rs hrs
    exact aes_ok rs hnd h8 hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

theorem aesDec_blkOk : BlkOk aesDec (Spec.Aes.invCipher (nr s₀) (sch s₀)) (KPd s₀) :=
  fun rs hrs s ⟨hK, hrdi, _, hrsi, hr10⟩ => by
    obtain ⟨hnd, h8⟩ := regs_nodup rs hrs
    exact aesDec_ok rs hnd h8 hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

/-- The return address is not in the data. -/
theorem ret_dR : ∀ r ∈ [dR s₀], (retR s₀).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_d

/-- … nor in the scratch buffer. -/
theorem ret_dS (hs : PreS s₀) : ∀ r ∈ [dR s₀, scrR s₀], (retR s₀).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.ret_d
  · exact hs.ret_scr

omit hp in
/-- From the state after the loops, which changed memory only in `rs`, apart
from the return address, the postcondition. -/
theorem post_of {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s : State} (hI : Inv KP (F (nr s₀) (sch s₀)) s₀ (nb s₀) (nb s₀) s) {rs : List Region}
    (hfr : Frame rs s₀.mem s.mem) (hret : ∀ r ∈ rs, (retR s₀).Disjoint r) :
    gprPreserved s₀ s ∧ (Proof.Aes.blocksX86_64 F).post s₀ s := by
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · exact hfr.readW (Region.contains_self _ _) hret (by decide)
  · show Spec.Aes.statesAt s.mem (dp s₀) (nb s₀) = _
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk := List.mem_range.mp hk
    have := hI.blocks k hk
    simp only [hk, ite_true] at this
    exact this

end

/-- `KP`, and memory changed only in the data since `s₀`: the loops keep both. -/
def KPf (KP : State → Prop) (s₀ : State) (s : State) : Prop := KP s ∧ Frame [dR s₀] s₀.mem s.mem

theorem Stable.frame {KP : State → Prop} {s₀ : State} (h : Stable KP s₀) : Stable (KPf KP s₀) s₀ :=
  fun s s' ⟨hk, hm⟩ hg hrd hwr hf => ⟨h s s' hk hg hrd hwr hf, hm.trans hf⟩

theorem BlkOk.frame {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State}
    {KP : State → Prop} (h : BlkOk f F KP) (s₀ : State) : BlkOk f F (KPf KP s₀) :=
  fun rs hrs s hk => h rs hrs s hk.1

/-- `KP`, and memory changed only in the data and in `R` since `s₀`: the
loops keep both, where `R` is what ran before them may have written. -/
def KPw (R : Region) (KP : State → Prop) (s₀ : State) (s : State) : Prop :=
  KP s ∧ Frame [dR s₀, R] s₀.mem s.mem

theorem Stable.frameW {KP : State → Prop} {s₀ : State} (R : Region) (h : Stable KP s₀) :
    Stable (KPw R KP s₀) s₀ :=
  fun s s' ⟨hk, hm⟩ hg hrd hwr hf =>
    ⟨h s s' hk hg hrd hwr hf, hm.trans (hf.mono fun r hr => by simp at hr; simp [hr])⟩

theorem BlkOk.frameW {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State}
    {KP : State → Prop} (h : BlkOk f F KP) (R : Region) (s₀ : State) : BlkOk f F (KPw R KP s₀) :=
  fun rs hrs s hk => h rs hrs s hk.1

/-- The keys and the regions at the start, for `KPe`. -/
theorem keys₀ {s₀ : State} (hp : Pre s₀) : Keys (nr s₀) (sch s₀) s₀ :=
  ⟨rfl, by rcases hp.rounds with h | h | h <;> omega_arith, fun j hj => ⟨sR s₀, by simp [hp.rd], by
    rw [AesNi.ofInt_natCast]; exact contains_offset (by rcases hp.rounds with h | h | h <;> omega_arith)
      (by rcases hp.rounds with h | h | h <;> omega_arith)⟩⟩

theorem encrypt_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Aes.X86_64.AesNi.encryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s₀ s' ∧
        Frame [dR s₀] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (blocksLoad_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁, _, cf₁⟩ => ?_)
  have hI₁ : Inv (KPf (KPe s₀) s₀) (Spec.Aes.cipher (nr s₀) (sch s₀)) s₀ 0 0 s₁ :=
    { le := Nat.zero_le _
      kp := ⟨⟨keys_congr (keys₀ hp) (g₁ _ (by decide)) rd₁ wr₁ (by rw [m₁]), g₁ _ (by decide),
        g₁ _ (by decide), r10₁⟩, by rw [m₁]; exact Frame.refl _ _⟩
      gpr := fun r _ _ h3 => g₁ r h3
      r10 := r10₁
      rdx := by rw [g₁ _ (by decide)]; simp [bAddr]
      rcx := by rw [g₁ _ (by decide)]; simp [nb]
      frame := by rw [m₁]; exact Frame.refl _ _
      blocks := fun k _ => by simp [m₁]
      rd := rd₁
      wr := wr₁ }
  exact WP.mono (tail_ok hp (kpe_stable hp).frame ((aes_blkOk hp).frame s₀) hI₁ (by simpa using cf₁))
    fun s hI => ⟨(post_of hI hI.kp.2 (ret_dR hp)).1, (post_of hI hI.kp.2 (ret_dR hp)).2, hI.kp.2⟩

theorem decrypt_correct {s₀ : State} (hp : Pre s₀) (hs : PreS s₀) :
    WP isa Impl.Aes.X86_64.AesNi.decryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s₀ s' ∧
        Frame [dR s₀, ⟨s₀.gpr .r8, 224⟩] s₀.mem s'.mem := by
  have hscr : (scrR s₀) ∈ s₀.wr := by rw [hs.wr]; simp
  have hsch : (sR s₀) ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by rw [hp.rd]; simp)
  refine WP.seq (WP.mono (imcKeys_ok hp.rounds (by simp) ⟨_, hscr, Region.contains_self _ _⟩ hsch hs.s_scr)
    fun s₁ ⟨S, hS₁, hcov⟩ => ?_)
  have hK₁ := dKeys_of_imc (keys₀ hp) ⟨_, hscr, Region.contains_self _ _⟩ hs.s_scr hS₁ hcov
  refine WP.seq (WP.mono (blocksLoad_ok s₁) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, _, cf₂⟩ => ?_)
  have g : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂ r h, hS₁.gpr]
  have hI₂ : Inv (KPw ⟨s₀.gpr .r8, 224⟩ (KPd s₀) s₀) (Spec.Aes.invCipher (nr s₀) (sch s₀)) s₀ 0 0 s₂ :=
    { le := Nat.zero_le _
      kp := ⟨⟨dkeys_congr hK₁ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ (by rw [m₂])
          (fun _ _ _ => by rw [m₂]), g _ (by decide), g _ (by decide), g _ (by decide),
        by rw [r10₂, hS₁.gpr]⟩, by rw [m₂]; exact hS₁.lo.mono fun r hr => by simp at hr; simp [hr]⟩
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
            exact hs.d_scr.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)
      rd := by rw [rd₂, hS₁.rd]
      wr := by rw [wr₂, hS₁.wr] }
  have hcf : s₂.cf = some (decide (nb s₀ - 0 < 8)) := by
    rw [cf₂, hS₁.gpr]; simp [nb]
  exact WP.mono (tail_ok hp ((kpd_stable hp hs).frameW _) ((aesDec_blkOk hp).frameW _ s₀) hI₂ hcf)
    fun s hI => ⟨(post_of hI hI.frame (ret_dS hp hs)).1, (post_of hI hI.frame (ret_dS hp hs)).2, hI.kp.2⟩

end Ecb

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.encrypt_correct (Ecb.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2.1⟩

theorem encryptBlocksF_correct (s : State) (hs : (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64F Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.encrypt_correct (Ecb.preF_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2.1⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.decrypt_correct (Ecb.pre_of s hs) (Ecb.preS_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2.1⟩

/-- Whatever the precondition: the public registers alone fix the trace. -/
theorem encryptBlocks_ctP {P : State → Prop} :
    ConstantTime isa P (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.AesNi.encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.AesNi.encryptBlocks := encryptBlocks_ctP

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub Impl.Aes.X86_64.AesNi.decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_implies :
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).Implies (Proof.Aes.encryptBlocksRoundsContract X86_64.abi) := by
  sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
    X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat

theorem encryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.encryptBlocks (Proof.Aes.encryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct encryptBlocks_implies

/-- A run of an encryption that changes memory only in the data writes none of
`scratch` (`Artifact.written`). -/
theorem written_of_frame {s s' : State} (hp : Ecb.PreS s) (hf : Frame [Ecb.dR s] s.mem s'.mem) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  simp [Sig.writtenWithin, X86_64.abi, X86_64.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  intro i h
  have h' : i < 2048 := by simpa [Elem.size] using h
  refine hf _ fun r hr hc => ?_
  rw [List.mem_singleton] at hr
  subst hr
  exact hp.d_scr _ hc (Offset.contains_base _ (by omega_using [h']) (by omega_using [h']))

theorem encryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.encryptBlocksRoundsContract X86_64.abi).pre s)
    (he : Exec isa Impl.Aes.X86_64.AesNi.encryptBlocks s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  have hp := Ecb.pre_of s (encryptBlocks_implies.pre s hs)
  obtain ⟨t', s'', he', h⟩ := Ecb.encrypt_correct hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact written_of_frame (Ecb.preS_of s (encryptBlocks_implies.pre s hs)) h.2.2

theorem decryptBlocks_implies :
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).Implies (Proof.Aes.decryptBlocksRoundsContract X86_64.abi) := by
  sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
    X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat

theorem decryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.decryptBlocks (Proof.Aes.decryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct decryptBlocks_implies

/-- A run of a decryption that changes memory only in the data and the first
224 bytes of `scratch`, its inverse key schedule, writes none of `scratch`
from there on (`Artifact.written`). -/
theorem written_of_frameKeys {s s' : State} (hp : Ecb.PreS s)
    (hf : Frame [Ecb.dR s, ⟨s.gpr .r8, 224⟩] s.mem s'.mem) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 224)] s s' := by
  simp [Sig.writtenWithin, X86_64.abi, X86_64.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  intro i hi hlo
  have hib : i < 2048 := by simpa [Elem.size] using hlo
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.d_scr _ hc (Offset.contains_base _ (by omega_using [hib]) (by omega_using [hib]))
  · change (s.gpr .r8 + BitVec.ofNat 64 i - s.gpr .r8).toNat + 1 ≤ 224 at hc
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hib])] at hc
    omega_using [hi, hc]

theorem decryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.decryptBlocksRoundsContract X86_64.abi).pre s)
    (he : Exec isa Impl.Aes.X86_64.AesNi.decryptBlocks s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 224)] s s' := by
  have hp := Ecb.pre_of s (decryptBlocks_implies.pre s hs)
  obtain ⟨t', s'', he', h⟩ := Ecb.decrypt_correct hp (Ecb.preS_of s (decryptBlocks_implies.pre s hs))
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact written_of_frameKeys (Ecb.preS_of s (decryptBlocks_implies.pre s hs)) h.2.2

end VG.Proof.Aes.X86_64.AesNi

end

end

/-!
# VAES: encryption and decryption of whole blocks

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86_64.VaesBlocks.encryptBlocks` and `decryptBlocks` against the
contracts of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, through
`Proof.Aes.blocksX86_64`, as `AesNi.encryptBlocks_verified` does. The
sixteen-block loop keeps the AES-NI loops' invariant (`AesNi.Ecb.Inv`, which
says nothing of the vector registers): lane `l` of block register `k` holds
data block `c + 2k + l` (`loadData_ok`, `storeData_ok`); after it,
`vzeroupper` keeps the invariant, and the AES-NI loops finish
(`AesNi.Ecb.tail_ok`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.VaesBlocks

open VG VG.X86_64
open VG.Impl.Aes.X86_64.VaesBlocks (loadData storeData blocksLoad blocks16 blocks)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Aes.X86_64.Vaes (regs8)
open VG.Proof.Aes.X86_64.AesNi (st ea_at ofInt_natCast stateAt_eq inRegions_wr contains_offset
  imcKeys_ok dKeys_of_imc)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi extract_lo extract_hi)
open VG.Proof.Aes.X86_64.AesNi.Ecb (Pre PreS Inv Stable sp nr dp nb dR scrR bAddr orig sch KPe KPd run_in run_sep
  beq_ofNat_zero' tail_ok post_of ret_dR ret_dS keys₀ kpe_stable kpd_stable aes_blkOk aesDec_blkOk keys_congr dkeys_congr
  pre_of)

/-! ## Two blocks in each register -/

/-- Load the 32 bytes at `rdx + d` into `b`. -/
theorem load1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 b (at_ .rdx d)]) s fun s' =>
      s'.lane b 0 = s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 128 ∧
      s'.lane b 1 = s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 16) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let v := s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 256
  rw [WP.block_cons_iff]
  refine ⟨s.setV .l256 b (v.extractLsb' 0 128) (v.extractLsb' 128 128), by
    simp only [isa, exec, State.load256, ea_at, hin, ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  refine ⟨by simp [State.lane_setV256, v, load256_lo], by simp [State.lane_setV256, v, load256_hi],
    by simp, by simp, by simp, by simp, fun r hr l _ => by simp [State.lane_setV256, hr]⟩

/-- Store `b` to the 32 bytes at `rdx + d`. -/
theorem store1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquStore .l256 (at_ .rdx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) (s.lane b 1 ++ s.lane b 0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  rw [WP.block_cons_iff]
  refine ⟨s.setMem (s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) (s.ymm b)), by
    simp only [isa, exec, State.store256_eq, ea_at, hin, ite_true], WP.block_nil ?_⟩
  exact ⟨by simp [State.ymm_eq], by simp, by simp, by simp, fun _ _ => by simp⟩

/-- The two blocks of a 32-byte write. -/
theorem stateAt_write_lo (m : Mem) (a : Addr) (lo hi : BitVec 128) :
    Spec.Aes.stateAt (m.writeW a (hi ++ lo)) a = st lo := by
  have e := readW_writeW_inside m a (hi ++ lo) (k := 0) (n := 16) (by decide) (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] at e
  rw [stateAt_eq, e, extract_lo]

theorem stateAt_write_hi (m : Mem) (a : Addr) (lo hi : BitVec 128) :
    Spec.Aes.stateAt (m.writeW a (hi ++ lo)) (a + BitVec.ofNat 64 16) = st hi := by
  have e := readW_writeW_inside m a (hi ++ lo) (k := 16) (n := 16) (by decide) (by decide)
  simp only [Nat.reduceMul] at e
  rw [stateAt_eq, e, extract_hi]

/-- Block `2j + l` is lane `l` of the 32 bytes at `32 j`. -/
theorem addr_lane (p : Addr) (j l : Nat) (hl : l < 2) :
    p + BitVec.ofNat 64 (16 * (2 * j + l)) =
      if l = 0 then p + BitVec.ofInt 64 ((32 * j : Nat) : Int)
      else p + BitVec.ofInt 64 ((32 * j : Nat) : Int) + BitVec.ofNat 64 16 := by
  rw [AesNi.ofInt_natCast]
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [ite_true]; congr 2; omega_arith
  · simp only [Nat.one_ne_zero, ite_false]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith

theorem loadData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) :
    WP isa (.block (loadData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        st (s'.lane regs[k] l) =
          Spec.Aes.stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (2 * (j + k) + l)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega_arith)
    rw [Nat.add_zero] at hin0
    refine WP.mono (load1_ok b (32 * j) s hin0)
      fun s₁ ⟨lo₁, hi₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact hin (k + 1) (by omega_arith)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, addr_lane _ _ _ hl, stateAt_eq]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [lo₁]
        · simp only [Nat.one_ne_zero, ite_false]; rw [hi₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk) l hl, show j + 1 + k = j + (k + 1) by omega_arith]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2 l hl, o₁ r hr.1 l hl]

theorem storeData_ok (regs : List XReg) (j : Nat) (s : State)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hw : (s.gpr .rdx).toNat + 32 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (storeData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        Spec.Aes.stateAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) =
          st (s.lane regs[k] l)) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hw
    rw [storeData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega_arith)
    rw [Nat.add_zero] at hin0
    refine WP.mono (store1_ok b (32 * j) s hin0)
      fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega_arith]; exact hin (k + 1) (by omega_arith))
      (by rw [hrdx]; omega_arith)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    rw [AesNi.ofInt_natCast] at m₁
    -- Blocks `2j` and `2j + 1` are not in the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (2 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [AesNi.off_toNat _ _ (by omega_arith)] at h₁ h₂
      have := (a - s.gpr .rdx).isLt
      omega_arith
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r l => (hx r l).trans (x₁ r l)⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [stateAt_eq, hf.readW (Region.contains_self _ _) (hdj l hl) (by decide), ← stateAt_eq, m₁]
        rw [addr_lane _ _ _ hl, AesNi.ofInt_natCast]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [stateAt_write_lo]
        · simp only [Nat.one_ne_zero, ite_false]; rw [stateAt_write_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega_arith, hb k (by simpa using hk) l hl, x₁]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [AesNi.off_toNat _ _ (by omega_arith)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega_arith

/-! ## The sixteen-block loop, for any transformation of both lanes -/

/-- `f` computes `F` on both lanes of each of `ymm0`–`ymm7`. -/
def BlkOk16 (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ s, KP s → WP isa (f regs8) s fun s' =>
    (∀ b ∈ regs8, ∀ l < 2, st (s'.lane b l) = F (st (s.lane b l))) ∧ YFrame (.xmm8 :: regs8) s s'

theorem BlkOk16.frame {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State}
    {KP : State → Prop} (h : BlkOk16 f F KP) (s₀ : State) : BlkOk16 f F (AesNi.Ecb.KPf KP s₀) :=
  fun s hk => h s hk.1

theorem BlkOk16.frameW {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State}
    {KP : State → Prop} (h : BlkOk16 f F KP) (R : Region) (s₀ : State) :
    BlkOk16 f F (AesNi.Ecb.KPw R KP s₀) :=
  fun s hk => h s hk.1

section Loops

variable {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
  {s₀ : State} (hp : Pre s₀) (hst : Stable KP s₀) (hf : BlkOk16 f F KP)
include hp hst hf

/-- The sixteen-block body. -/
theorem body16_ok {c : Nat} (hc : c + 16 ≤ nb s₀) {s : State} (hI : Inv KP F s₀ c c s) :
    WP isa (blocks16 f) s fun s' => Inv KP F s₀ (c + 16) (c + 16) s' ∧
      s'.cf = some (decide (nb s₀ - (c + 16) < 16)) := by
  have hnd : regs8.Nodup := by decide
  have hlen : regs8.length = 8 := rfl
  have hw := hp.wrap
  have hn := hp.nb_lt
  have hrdxN : (s.gpr .rdx).toNat = (dp s₀).toNat + 16 * c := by
    rw [hI.rdx, bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  have addr : ∀ (t : State), t.gpr .rdx = s.gpr .rdx → ∀ k,
      t.gpr .rdx + BitVec.ofInt 64 ((32 * (0 + k) : Nat) : Int) = bAddr s₀ (c + 2 * k) :=
    fun t ht k => by
      rw [ht, hI.rdx, AesNi.ofInt_natCast, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 32 * (0 + k) = 16 * (c + 2 * k) by omega_arith]
  have addr' : ∀ k l, s.gpr .rdx + BitVec.ofNat 64 (16 * (2 * (0 + k) + l)) = bAddr s₀ (c + (2 * k + l)) :=
    fun k l => by
      rw [hI.rdx, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (2 * (0 + k) + l) = 16 * (c + (2 * k + l)) by omega_arith]
  have hout : ∀ k, k < 8 → InRegions s.wr (bAddr s₀ (c + 2 * k)) 32 := fun k hk =>
    ⟨dR s₀, by obtain ⟨_, hw⟩ := hp.wr; simp [hI.wr, hw], by
      rw [bAddr]; exact contains_offset (by omega_arith) (by omega_arith)⟩
  refine WP.seq (WP.mono (loadData_ok regs8 0 s hnd fun k hk => by
      rw [addr s rfl]; obtain ⟨r, hr, h⟩ := hout k hk
      exact ⟨r, List.mem_append_right _ hr, h⟩) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < regs8.length), ∀ l < 2,
      st (s₂.lane regs8[k] l) = F (orig s₀ (c + (2 * k + l))) := fun k h l hl => by
    rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl, addr', hI.blocks _ (by omega_arith)]
    simp only [show ¬ c + (2 * k + l) < c by omega_arith, ite_false]
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok regs8 0 s₂ (fun k hk => by
      rw [addr s₂ hrdx₂, f₂.wr, wr₁]; exact hout k hk) (by rw [hrdx₂, hrdxN, hlen]; omega_arith))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hrdx₂] at fr₃
  rw [hrdx₂] at b₃
  rw [Nat.mul_zero, BitVec.add_zero, hI.rdx, hlen] at fr₃
  simp only [addr'] at b₃
  have fr₃' : Frame [dR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      exact run_in (d := dp s₀) (n := 16) hw hc (by simp only [Region.Contains, bAddr] at ha ⊢; omega_arith)⟩
  have g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  have hI₃ : Inv KP F s₀ (c + 16) c s₃ := by
    refine ⟨hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
      (by rw [wr₃, f₂.wr, wr₁]) fr₃', fun r h1 h2 h3 => by rw [g₃', hI.gpr r h1 h2 h3],
      by rw [g₃', hI.r10], by rw [g₃', hI.rdx], by rw [g₃', hI.rcx],
      hI.frame.trans (fr₃'.mono fun r hr => by simp at hr; simp [hr]), ?_,
      by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩
    intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 16) →
        Spec.Aes.stateAt s₃.mem (bAddr s₀ k) = Spec.Aes.stateAt s.mem (bAddr s₀ k) :=
      fun hn => by
        rw [stateAt_eq, stateAt_eq]
        exact congrArg st <| fr₃.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr
            subst hr
            intro a h₁ h₂
            simp only [Region.Contains, bAddr] at h₁ h₂
            exact run_sep (n := 16) (a := a) hw hk hc hn (by omega_arith) (by omega_arith)) (by decide)
    by_cases hlo : k < c
    · rw [out (by omega_arith), hI.blocks k hk]
      simp only [hlo, show k < c + 16 by omega_arith, ite_true]
    · by_cases hhi : k < c + 16
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega_arith⟩
        have hj : i / 2 < regs8.length := by rw [hlen]; omega_arith
        rw [b₃ (i / 2) hj (i % 2) (by omega_arith), ek (i / 2) hj (i % 2) (by omega_arith)]
        simp only [hhi, ite_true]
      · rw [out (by omega_arith), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]
  -- `add rdx, 256`, `sub rcx, 16` and `cmp rcx, 16`.
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hrdx := hI₃.rdx
  have hrcx := hI₃.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 16 = BitVec.ofNat 64 (nb s₀ - (c + 16)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega_arith
  refine ⟨{ hI₃ with
    kp := hst _ _ hI₃.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₃.gpr r h1 h2 h3]
    r10 := by simp [hI₃.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, bAddr]; bv_omega_arith
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - (c + 16) < 2 ^ 64 by omega_arith),
    show (16 : BitVec 64).toNat = 16 from rfl]

omit hf in
/-- `vzeroupper`, and the comparison that starts the AES-NI loops. -/
theorem mid_ok {c : Nat} {s : State} (hI : Inv KP F s₀ c c s) :
    WP isa (.block [.vop .vzeroupper, .alu .cmp .rcx (.imm 8)]) s fun s' =>
      Inv KP F s₀ c c s' ∧ s'.cf = some (decide (nb s₀ - c < 8)) := by
  have hn := hp.nb_lt
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, e8, hrcx, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨{ hI with kp := hst _ _ hI.kp (fun _ _ _ => rfl) rfl rfl (Frame.refl _ _) }, ?_⟩
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - c < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

end Loops

/-- The loops: sixteen blocks at a time through `f16`, then the AES-NI loops
through `f`. -/
theorem loops_ok {f16 f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s₀ : State} (hp : Pre s₀) (hst : Stable KP s₀) (hf16 : BlkOk16 f16 F KP)
    (hf : AesNi.Ecb.BlkOk f F KP) {s₁ : State} (hI₁ : Inv KP F s₀ 0 0 s₁)
    (hcf : s₁.cf = some (decide (nb s₀ < 16))) :
    WP isa (.seq (.ite .b (.block []) (.loop (blocks16 f16) .ae))
      (.seq (.block [.vop .vzeroupper, .alu .cmp .rcx (.imm 8)]) (Impl.Aes.X86_64.AesNi.blocksTail f))) s₁
      (Inv KP F s₀ (nb s₀) (nb s₀)) := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 16 ∧ Inv KP F s₀ c c s) ?_
    fun s₂ ⟨c, _, hI₂⟩ => WP.seq (WP.mono (mid_ok hp hst hI₂) fun s₃ ⟨hI₃, hcf₃⟩ =>
      tail_ok hp hst hf hI₃ hcf₃))
  refine WP.ite (decide (nb s₀ < 16)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨0, by simpa using h, hI₁⟩
  · let I16 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 16 ≤ nb s₀ ∧ Inv KP F s₀ c c s
    have hstep : ∀ m s, I16 m s → WP isa (blocks16 f16) s (fun s' =>
        (eval .ae s' = some false ∧ ∃ c, nb s₀ - c < 16 ∧ Inv KP F s₀ c c s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I16 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body16_ok hp hst hf16 hc hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - (c + 16) < 16
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 16, hlt, hI'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 16), by omega_arith, c + 16, rfl, by omega_arith, hI'⟩
    exact WP.loop (M := isa) I16 hstep (nb s₀) s₁ ⟨0, rfl, by simp at h; omega_arith, hI₁⟩

/-! ## The two functions -/

theorem blocksLoad_ok (s : State) :
    WP isa (.block blocksLoad) s fun s' =>
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rcx).toNat < 16)) := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, blocksLoad, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, e16,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by bv_omega_arith, fun r h => by simp [h], trivial, trivial, trivial, ?_⟩
  simp

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem aes16_blkOk : BlkOk16 Impl.Aes.X86_64.Vaes.aes (Spec.Aes.cipher (nr s₀) (sch s₀)) (KPe s₀) :=
  fun s ⟨hK, hrdi, hrsi, hr10⟩ =>
    Vaes.aes_ok regs8 (by decide) (by decide) hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

theorem aesDec16_blkOk :
    BlkOk16 Impl.Aes.X86_64.VaesBlocks.aesDec (Spec.Aes.invCipher (nr s₀) (sch s₀)) (KPd s₀) :=
  fun s ⟨hK, hrdi, _, hrsi, hr10⟩ =>
    aesDec_ok regs8 (by decide) (by decide) hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

end

theorem encrypt_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Aes.X86_64.VaesBlocks.encryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s₀ s' ∧
        Frame [dR s₀] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (blocksLoad_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁, cf₁⟩ => ?_)
  have hI₁ : Inv (AesNi.Ecb.KPf (KPe s₀) s₀) (Spec.Aes.cipher (nr s₀) (sch s₀)) s₀ 0 0 s₁ :=
    { le := Nat.zero_le _
      kp := ⟨⟨keys_congr (keys₀ hp) (g₁ _ (by decide)) rd₁ wr₁ (by rw [m₁]), g₁ _ (by decide),
        g₁ _ (by decide), r10₁⟩, by rw [m₁]; exact Frame.refl _ _⟩
      gpr := fun r _ _ h3 => g₁ r h3
      r10 := r10₁
      rdx := by rw [g₁ _ (by decide)]; simp [bAddr]
      rcx := by rw [g₁ _ (by decide)]; simp [nb]
      frame := by rw [m₁]; exact Frame.refl _ _
      blocks := fun k _ => by simp [m₁]
      rd := rd₁
      wr := wr₁ }
  exact WP.mono (loops_ok hp (kpe_stable hp).frame ((aes16_blkOk hp).frame s₀) ((aes_blkOk hp).frame s₀)
      hI₁ (by simpa using cf₁))
    fun s hI => ⟨(post_of hI hI.kp.2 (ret_dR hp)).1, (post_of hI hI.kp.2 (ret_dR hp)).2, hI.kp.2⟩

theorem decrypt_correct {s₀ : State} (hp : Pre s₀) (hs : PreS s₀) :
    WP isa Impl.Aes.X86_64.VaesBlocks.decryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s₀ s' ∧
        Frame [dR s₀, ⟨s₀.gpr .r8, 224⟩] s₀.mem s'.mem := by
  have hscr : (scrR s₀) ∈ s₀.wr := by rw [hs.wr]; simp
  have hsch : (AesNi.Ecb.sR s₀) ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by rw [hp.rd]; simp)
  refine WP.seq (WP.mono (imcKeys_ok hp.rounds (by simp) ⟨_, hscr, Region.contains_self _ _⟩ hsch hs.s_scr)
    fun s₁ ⟨S, hS₁, hcov⟩ => ?_)
  have hK₁ := dKeys_of_imc (keys₀ hp) ⟨_, hscr, Region.contains_self _ _⟩ hs.s_scr hS₁ hcov
  refine WP.seq (WP.mono (blocksLoad_ok s₁) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  have g : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂ r h, hS₁.gpr]
  have hI₂ : Inv (AesNi.Ecb.KPw ⟨s₀.gpr .r8, 224⟩ (KPd s₀) s₀) (Spec.Aes.invCipher (nr s₀) (sch s₀)) s₀ 0 0
      s₂ :=
    { le := Nat.zero_le _
      kp := ⟨⟨dkeys_congr hK₁ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ (by rw [m₂])
          (fun _ _ _ => by rw [m₂]), g _ (by decide), g _ (by decide), g _ (by decide),
        by rw [r10₂, hS₁.gpr]⟩, by rw [m₂]; exact hS₁.lo.mono fun r hr => by simp at hr; simp [hr]⟩
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
            exact hs.d_scr.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)
      rd := by rw [rd₂, hS₁.rd]
      wr := by rw [wr₂, hS₁.wr] }
  have hcf : s₂.cf = some (decide (nb s₀ < 16)) := by
    rw [cf₂, hS₁.gpr]
  exact WP.mono (loops_ok hp ((kpd_stable hp hs).frameW _) ((aesDec16_blkOk hp).frameW _ s₀)
      ((aesDec_blkOk hp).frameW _ s₀) hI₂ hcf)
    fun s hI => ⟨(post_of hI hI.frame (ret_dS hp hs)).1, (post_of hI hI.frame (ret_dS hp hs)).2, hI.kp.2⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.VaesBlocks.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := encrypt_correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2.1⟩

theorem encryptBlocksF_correct (s : State) (hs : (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.VaesBlocks.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64F Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := encrypt_correct (AesNi.Ecb.preF_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2.1⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.VaesBlocks.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := decrypt_correct (pre_of s hs) (AesNi.Ecb.preS_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2.1⟩

/-- Whatever the precondition: the public registers alone fix the trace. -/
theorem encryptBlocks_ctP {P : State → Prop} :
    ConstantTime isa P (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.VaesBlocks.encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.VaesBlocks.encryptBlocks := encryptBlocks_ctP

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub Impl.Aes.X86_64.VaesBlocks.decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.VaesBlocks.encryptBlocks
      (Proof.Aes.encryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct AesNi.encryptBlocks_implies

theorem encryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.encryptBlocksRoundsContract X86_64.abi).pre s)
    (he : Exec isa Impl.Aes.X86_64.VaesBlocks.encryptBlocks s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  have hp := pre_of s (AesNi.encryptBlocks_implies.pre s hs)
  obtain ⟨t', s'', he', h⟩ := encrypt_correct hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact AesNi.written_of_frame (AesNi.Ecb.preS_of s (AesNi.encryptBlocks_implies.pre s hs)) h.2.2

theorem decryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.VaesBlocks.decryptBlocks
      (Proof.Aes.decryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct AesNi.decryptBlocks_implies

theorem decryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.decryptBlocksRoundsContract X86_64.abi).pre s)
    (he : Exec isa Impl.Aes.X86_64.VaesBlocks.decryptBlocks s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 224)] s s' := by
  have hp := pre_of s (AesNi.decryptBlocks_implies.pre s hs)
  obtain ⟨t', s'', he', h⟩ := decrypt_correct hp (AesNi.Ecb.preS_of s (AesNi.decryptBlocks_implies.pre s hs))
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact AesNi.written_of_frameKeys (AesNi.Ecb.preS_of s (AesNi.decryptBlocks_implies.pre s hs)) h.2.2

end VG.Proof.Aes.X86_64.VaesBlocks

end

end

/-!
# Implementations of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` on x86-64

A `BlocksImpl` is what a function that encrypts and decrypts whole blocks
with AES needs of them, so that its proof holds for every implementation:
each is a variant of the interface `AesBlocks` on x86-64
(`Variants/AesBlocks/X86_64/`), and each caller (in
`Generic/AesBlocks/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both functions are proven against the same contract,
`Proof.Aes.blocksX86_64` (with `Spec.Aes.cipher` and `Spec.Aes.invCipher`),
and make no calls. Each states how much of `scratch` its functions may write
(`encWritten`, `decWritten`), so that its callers zero only that. They come with the implementation of `vg_aes_expand_key`
that goes with them (with the same suffix and CPU features), for the callers
that also expand the key, proven against `Proof.Aes.expandKeyX86_64`.
An implementation also gives the residue analyses of the functions over it
that the analysis handles (`cfb8EncRes`, `cfb8DecRes`, `ecbEncRes`): those
instances then return without secret residue (`X86_64.RScrub.withScrub`).
One whose encryption and key expansion never touch their scratch buffers
gives their contracts without them (`free`), and the analysis of
`vg_aes_ocb_init` over it with no working space for them (`ocbInitRes`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64

open VG.X86_64

/-- What an implementation whose encryption and key expansion never touch
their scratch buffers gives: their contracts without them
(`Proof.Aes.blocksX86_64F`, `AesNi.Key.expandKey3X86_64`), so that a caller
of those alone needs no working space for them. -/
structure BlocksFree (enc : Impl.Aes.X86_64.Blocks) (expand : Impl.Aes.X86_64.ExpandKey) : Type where
  encOk : ∀ s, (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64F Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64F Spec.Aes.cipher).pub enc.code
  expandOk : ∀ s, AesNi.Key.expandKey3X86_64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ AesNi.Key.expandKey3X86_64.post s s'
  expandCt : ConstantTime isa AesNi.Key.expandKey3X86_64.pre AesNi.Key.expandKey3X86_64.pub expand.code

/-- `vg_aes_ocb_init`'s code over `enc`, `dec` and `expand` when encryption
and the key expansion need no working space (`BlocksFree`): a frame of only
the 24 bytes `init` writes itself. -/
def ocbInitCodeF (enc dec : Impl.Aes.X86_64.Blocks) (expand : Impl.Aes.X86_64.ExpandKey) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 32 .rcx (Impl.AesOcb.X86_64.init ⟨enc, dec, expand⟩)

/-- An implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
on x86-64, and of `vg_aes_expand_key`. -/
structure BlocksImpl where
  /-- `vg_aes_encrypt_blocks`: its symbol and code. -/
  enc : Impl.Aes.X86_64.Blocks
  encDepth : enc.code.depth = 0
  encOk : ∀ s, (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s'
  encCt : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub enc.code
  encNosp : NoSp enc.code
  encMxcsr : enc.code.allInstrs (fun i => !loadsMxcsr i) = true
  encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true
  encNoStack : enc.code.x86_64Depth = 0
  /-- `vg_aes_decrypt_blocks`: its symbol and code. -/
  dec : Impl.Aes.X86_64.Blocks
  decDepth : dec.code.depth = 0
  decOk : ∀ s, (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s'
  decCt : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub dec.code
  decNosp : NoSp dec.code
  decMxcsr : dec.code.allInstrs (fun i => !loadsMxcsr i) = true
  decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true
  decNoStack : dec.code.x86_64Depth = 0
  /-- `enc` writes no byte of `scratch` at offset `encWritten` or beyond:
  its callers need to zero only the first `encWritten` bytes. -/
  encWritten : Nat
  encWrittenLe : encWritten ≤ 2048
  encWrittenOk : ∀ s t s', (Proof.Aes.encryptBlocksRoundsContract X86_64.abi).pre s →
    Exec isa enc.code s t s' →
      Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", encWritten)] s s'
  /-- `dec` writes no byte of `scratch` at offset `decWritten` or beyond. -/
  decWritten : Nat
  decWrittenLe : decWritten ≤ 2048
  decWrittenOk : ∀ s t s', (Proof.Aes.decryptBlocksRoundsContract X86_64.abi).pre s →
    Exec isa dec.code s t s' →
      Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", decWritten)] s s'
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.X86_64.ExpandKey
  expandDepth : expand.code.depth = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86_64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub expand.code
  expandNosp : NoSp expand.code
  expandMxcsr : expand.code.allInstrs (fun i => !loadsMxcsr i) = true
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
  expandNoStack : expand.code.x86_64Depth = 0
  /-- The level of the vector instructions of `enc`, `dec` and `expand`. -/
  level : Impl.Scrub.X86_64.VecLevel
  /-- What the cleanup of a function that calls them needs of their code, at
  that level (`X86_64.Scrub.calleeSide`), evaluated here, once. -/
  encSide : X86_64.Scrub.calleeSide enc.code level.level 0 = true
  decSide : X86_64.Scrub.calleeSide dec.code level.level 0 = true
  expandSide : X86_64.Scrub.calleeSide expand.code level.level 0 = true
  /-- The bytes of `scratch` `enc` and `dec` write, among those the stubs of
  their callers' code take. -/
  writtenOk : (encWritten = 0 ∨ encWritten = 2048) ∧ (decWritten = 224 ∨ decWritten = 2048) := by decide
  /-- The residue analysis of `vg_aes_cfb8_encrypt` over it, if the analysis
  handles it. -/
  cfb8EncRes : Option (RScrub.Analysed Spec.Cfb8.aesEncryptApi.sig 8 []
    (Impl.AesCfb8.X86_64.encrypt enc)) := none
  /-- The residue analysis of `vg_aes_cfb8_decrypt` over it, if the analysis
  handles it. -/
  cfb8DecRes : Option (RScrub.Analysed Spec.Cfb8.aesDecryptApi.sig 8 []
    (Impl.AesCfb8.X86_64.decrypt enc)) := none
  /-- The residue analysis of `vg_aes_cfb128_encrypt` over it, if the
  analysis handles it. -/
  cfbEncRes : Option (RScrub.Analysed Spec.Cfb.aesEncryptApi.sig 8 []
    (Impl.AesCfb.X86_64.encrypt enc)) := none
  /-- The residue analysis of `vg_aes_cfb128_decrypt` over it, if the
  analysis handles it. -/
  cfbDecRes : Option (RScrub.Analysed Spec.Cfb.aesDecryptApi.sig 8 []
    (Impl.AesCfb.X86_64.decrypt enc)) := none
  /-- The residue analysis of `vg_aes_ofb` over it, if the analysis handles
  it. -/
  ofbRes : Option (RScrub.Analysed Spec.Ofb.aesApi.sig 8 [] (Impl.AesOfb.X86_64.crypt enc)) := none
  /-- The residue analysis of `vg_aes_ecb_encrypt` as its `enc` alone, if
  the analysis handles it. -/
  ecbEncRes : Option (RScrub.Analysed Spec.AesEcb.encryptApi.sig 0 [] enc.code) := none
  /-- The contracts of encryption and the key expansion without a scratch
  buffer, if they never touch one. -/
  free : Option (BlocksFree enc expand) := none
  /-- The residue analysis of `vg_aes_ocb_init` over it, without working
  space for it (`free`), if the analysis handles it. -/
  ocbInitRes : Option (RScrub.Analysed Spec.Ocb.initApi.sig 40 [] (ocbInitCodeF enc dec expand)) := none

namespace BlocksImpl

theorem nosp_of {c : Prog isa}
    (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

/-- Any run writes none of `scratch` from its end on. -/
theorem written_all (s s' : State) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 2048)] s s' := by
  simp [Sig.writtenWithin, X86_64.abi, X86_64.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits, Elem.size]
  intro i h1 h2
  omega

/-- The bitsliced implementation, `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks`, in the baseline ISA. -/
def scalar : BlocksImpl where
  enc := .encScalar
  encDepth := by lit_decide
  encOk := encryptBlocks_correct
  encCt := encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  encMxcsr := by lit_decide
  encSpSafe := Code.all_of_spTest (by lit_decide)
  encNoStack := by lit_decide
  dec := .decScalar
  decDepth := by lit_decide
  decOk := decryptBlocks_correct
  decCt := decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  decMxcsr := by lit_decide
  decSpSafe := Code.all_of_spTest (by lit_decide)
  decNoStack := by lit_decide
  encWritten := 2048
  encWrittenLe := Nat.le_refl _
  encWrittenOk := fun s _ s' _ _ => written_all s s'
  decWritten := 2048
  decWrittenLe := Nat.le_refl _
  decWrittenOk := fun s _ s' _ _ => written_all s s'
  suffix := ""
  features := []
  expand := .scalar
  expandDepth := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandNosp := Ctr32Impl.expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_spTest (by lit_decide)
  expandNoStack := by lit_decide
  level := .sse
  encSide := by lit_decide
  decSide := by lit_decide
  expandSide := by lit_decide

/-- The AES-NI implementation, `vg_aes_encrypt_blocks_aesni` and
`vg_aes_decrypt_blocks_aesni`, with `vg_aes_expand_key_aesni`. -/
def aesni : BlocksImpl where
  enc := .encAesni
  encDepth := by lit_decide
  encOk := AesNi.encryptBlocks_correct
  encCt := AesNi.encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  encMxcsr := by lit_decide
  encSpSafe := Code.all_of_spTest (by lit_decide)
  encNoStack := by lit_decide
  dec := .decAesni
  decDepth := by lit_decide
  decOk := AesNi.decryptBlocks_correct
  decCt := AesNi.decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  decMxcsr := by lit_decide
  decSpSafe := Code.all_of_spTest (by lit_decide)
  decNoStack := by lit_decide
  encWritten := 0
  encWrittenLe := Nat.zero_le _
  encWrittenOk := AesNi.encryptBlocks_written
  decWritten := 224
  decWrittenLe := by decide
  decWrittenOk := AesNi.decryptBlocks_written
  free := some ⟨AesNi.encryptBlocksF_correct, AesNi.encryptBlocks_ctP, AesNi.Key.expandKey3_correct,
    AesNi.Key.expandKey3_ct⟩
  suffix := "_aesni"
  features := ["aes"]
  expand := .aesni
  expandDepth := by lit_decide
  expandOk := Ctr32Impl.aesni_expandKey_ok
  expandCt := Ctr32Impl.aesni_expandKey_ct
  expandNosp := Ctr32Impl.aesni_expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_spTest (by lit_decide)
  expandNoStack := by lit_decide
  level := .sse
  encSide := by lit_decide
  decSide := by lit_decide
  expandSide := by lit_decide

/-- The VAES implementation, `vg_aes_encrypt_blocks_vaes` and
`vg_aes_decrypt_blocks_vaes` (sixteen blocks at a time, then AES-NI's
loops), with `vg_aes_expand_key_aesni`. -/
def vaes : BlocksImpl where
  enc := .encVaes
  encDepth := by lit_decide
  encOk := VaesBlocks.encryptBlocks_correct
  encCt := VaesBlocks.encryptBlocks_ct
  encNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  encMxcsr := by lit_decide
  encSpSafe := Code.all_of_spTest (by lit_decide)
  encNoStack := by lit_decide
  dec := .decVaes
  decDepth := by lit_decide
  decOk := VaesBlocks.decryptBlocks_correct
  decCt := VaesBlocks.decryptBlocks_ct
  decNosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  decMxcsr := by lit_decide
  decSpSafe := Code.all_of_spTest (by lit_decide)
  decNoStack := by lit_decide
  encWritten := 0
  encWrittenLe := Nat.zero_le _
  encWrittenOk := VaesBlocks.encryptBlocks_written
  decWritten := 224
  decWrittenLe := by decide
  decWrittenOk := VaesBlocks.decryptBlocks_written
  free := some ⟨VaesBlocks.encryptBlocksF_correct, VaesBlocks.encryptBlocks_ctP,
    AesNi.Key.expandKey3_correct, AesNi.Key.expandKey3_ct⟩
  suffix := "_vaes"
  features := ["aes", "avx", "avx2", "vaes"]
  expand := .aesni
  expandDepth := by lit_decide
  expandOk := Ctr32Impl.aesni_expandKey_ok
  expandCt := Ctr32Impl.aesni_expandKey_ct
  expandNosp := Ctr32Impl.aesni_expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_spTest (by lit_decide)
  expandNoStack := by lit_decide
  level := .avx
  encSide := by lit_decide
  decSide := by lit_decide
  expandSide := by lit_decide

end BlocksImpl

end VG.Proof.Aes.X86_64
