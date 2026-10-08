import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks

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

namespace VG.Proof.Aes.X86_64.VaesBlocks

open VG VG.X86_64
open VG.Impl.Aes.X86_64.VaesBlocks (loadData storeData blocksLoad blocks16 blocks)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Aes.X86_64.Vaes (regs8)
open VG.Proof.Aes.X86_64.AesNi (st ea_at ofInt_natCast stateAt_eq inRegions_wr contains_offset
  imcKeys_ok dKeys_of_imc)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi extract_lo extract_hi)
open VG.Proof.Aes.X86_64.AesNi.Ecb (Pre Inv Stable sp nr dp nb dR scrR bAddr orig sch KPe KPd run_in run_sep
  beq_ofNat_zero' tail_ok post_of keys₀ kpe_stable kpd_stable aes_blkOk aesDec_blkOk keys_congr dkeys_congr
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
  rw [ofInt_natCast]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [ite_true]; congr 2; omega
  · simp only [Nat.one_ne_zero, ite_false]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

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
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (load1_ok b (32 * j) s hin0)
      fun s₁ ⟨lo₁, hi₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, addr_lane _ _ _ hl, stateAt_eq]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [lo₁]
        · simp only [Nat.one_ne_zero, ite_false]; rw [hi₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk) l hl, show j + 1 + k = j + (k + 1) by omega]
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
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (store1_ok b (32 * j) s hin0)
      fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    rw [ofInt_natCast] at m₁
    -- Blocks `2j` and `2j + 1` are not in the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (2 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [AesNi.off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .rdx).isLt
      omega
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r l => (hx r l).trans (x₁ r l)⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [stateAt_eq, hf.readW (Region.contains_self _ _) (hdj l hl) (by decide), ← stateAt_eq, m₁]
        rw [addr_lane _ _ _ hl, ofInt_natCast]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [stateAt_write_lo]
        · simp only [Nat.one_ne_zero, ite_false]; rw [stateAt_write_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega, hb k (by simpa using hk) l hl, x₁]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [AesNi.off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega

/-! ## The sixteen-block loop, for any transformation of both lanes -/

/-- `f` computes `F` on both lanes of each of `ymm0`–`ymm7`. -/
def BlkOk16 (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ s, KP s → WP isa (f regs8) s fun s' =>
    (∀ b ∈ regs8, ∀ l < 2, st (s'.lane b l) = F (st (s.lane b l))) ∧ YFrame (.xmm8 :: regs8) s s'

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
    rw [hI.rdx, bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have addr : ∀ (t : State), t.gpr .rdx = s.gpr .rdx → ∀ k,
      t.gpr .rdx + BitVec.ofInt 64 ((32 * (0 + k) : Nat) : Int) = bAddr s₀ (c + 2 * k) :=
    fun t ht k => by
      rw [ht, hI.rdx, ofInt_natCast, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 32 * (0 + k) = 16 * (c + 2 * k) by omega]
  have addr' : ∀ k l, s.gpr .rdx + BitVec.ofNat 64 (16 * (2 * (0 + k) + l)) = bAddr s₀ (c + (2 * k + l)) :=
    fun k l => by
      rw [hI.rdx, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (2 * (0 + k) + l) = 16 * (c + (2 * k + l)) by omega]
  have hout : ∀ k, k < 8 → InRegions s.wr (bAddr s₀ (c + 2 * k)) 32 := fun k hk =>
    ⟨dR s₀, by simp [hI.wr, hp.wr], by
      rw [bAddr]; exact contains_offset (by omega) (by omega)⟩
  refine WP.seq (WP.mono (loadData_ok regs8 0 s hnd fun k hk => by
      rw [addr s rfl]; obtain ⟨r, hr, h⟩ := hout k hk
      exact ⟨r, List.mem_append_right _ hr, h⟩) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < regs8.length), ∀ l < 2,
      st (s₂.lane regs8[k] l) = F (orig s₀ (c + (2 * k + l))) := fun k h l hl => by
    rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl, addr', hI.blocks _ (by omega)]
    simp only [show ¬ c + (2 * k + l) < c by omega, ite_false]
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeData_ok regs8 0 s₂ (fun k hk => by
      rw [addr s₂ hrdx₂, f₂.wr, wr₁]; exact hout k hk) (by rw [hrdx₂, hrdxN, hlen]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hrdx₂] at fr₃
  rw [hrdx₂] at b₃
  rw [Nat.mul_zero, BitVec.add_zero, hI.rdx, hlen] at fr₃
  simp only [addr'] at b₃
  have fr₃' : Frame [dR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      exact run_in (d := dp s₀) (n := 16) hw hc (by simp only [Region.Contains, bAddr] at ha ⊢; omega)⟩
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
            exact run_sep (n := 16) (a := a) hw hk hc hn (by omega) (by omega)) (by decide)
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + 16 by omega, ite_true]
    · by_cases hhi : k < c + 16
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
        have hj : i / 2 < regs8.length := by rw [hlen]; omega
        rw [b₃ (i / 2) hj (i % 2) (by omega), ek (i / 2) hj (i % 2) (by omega)]
        simp only [hhi, ite_true]
      · rw [out (by omega), hI.blocks k hk]
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
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₃ with
    kp := hst _ _ hI₃.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₃.gpr r h1 h2 h3]
    r10 := by simp [hI₃.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, bAddr]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - (c + 16) < 2 ^ 64 by omega),
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
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - c < 2 ^ 64 by omega),
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
      · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 16), by omega, c + 16, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I16 hstep (nb s₀) s₁ ⟨0, rfl, by simp at h; omega, hI₁⟩

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
  refine ⟨by bv_omega, fun r h => by simp [h], trivial, trivial, trivial, ?_⟩
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
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s₀ s' := by
  refine WP.seq (WP.mono (blocksLoad_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁, cf₁⟩ => ?_)
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
  exact WP.mono (loops_ok hp (kpe_stable hp) (aes16_blkOk hp) (aes_blkOk hp) hI₁ (by simpa using cf₁))
    fun s hI => post_of hp hI

theorem decrypt_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Aes.X86_64.VaesBlocks.decryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s₀ s' := by
  have hscr : (scrR s₀) ∈ s₀.wr := by rw [hp.wr]; simp
  have hsch : (AesNi.Ecb.sR s₀) ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by rw [hp.rd]; simp)
  refine WP.seq (WP.mono (imcKeys_ok hp.rounds (by simp) hscr hsch hp.s_scr)
    fun s₁ ⟨S, hS₁, hcov⟩ => ?_)
  have hK₁ := dKeys_of_imc (keys₀ hp) hscr hp.s_scr hS₁ hcov
  refine WP.seq (WP.mono (blocksLoad_ok s₁) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
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
  have hcf : s₂.cf = some (decide (nb s₀ < 16)) := by
    rw [cf₂, hS₁.gpr]
  exact WP.mono (loops_ok hp (kpd_stable hp) (aesDec16_blkOk hp) (aesDec_blkOk hp) hI₂ hcf)
    fun s hI => post_of hp hI

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.VaesBlocks.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := encrypt_correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.VaesBlocks.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := decrypt_correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.VaesBlocks.encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

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
      (Spec.Aes.encryptBlocksContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat)

theorem decryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.VaesBlocks.decryptBlocks
      (Spec.Aes.decryptBlocksContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat)

end VG.Proof.Aes.X86_64.VaesBlocks
