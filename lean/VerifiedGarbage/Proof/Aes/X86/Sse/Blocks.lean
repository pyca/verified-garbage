module

public import VerifiedGarbage.Proof.Aes.X86.Sse.Loops
public import VerifiedGarbage.Proof.Aes.X86.Sse.Rounds
public import VerifiedGarbage.Proof.Aes.X86.BlocksContract
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.Aes.X86.Sse
meta import VerifiedGarbage.Proof.Aes.X86.BlocksContract
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# AES on whole blocks, in SSE2 registers, on x86 (32-bit)

`blocks crypt8` runs `crypt8` on the blocks of the data, eight at a time.
`EcbInv`: the first `k` blocks of the data hold the results, the others are
as they were. Both functions are proven at once, for any `crypt8` with
`CryptOk` (`correct_blocks`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.Impl.Aes.X86.Sse VG.Proof.Aes
open VG.Impl.Aes.X86 (sb at_ argOp movI addI subI addR subR dbl movR)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_sub wp_subi wp_ldm wp_stm wp_cmpi wp_test
  toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## The data -/

/-- The data after `k` blocks: the first `k` of the `n` blocks at `D` are
`F`'s, the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

/-- `c` more blocks. -/
theorem ecbInv_patch {m₀ m : Mem} {D : Addr} {n k c : Nat} {F : Nat → Spec.Aes.State} {v : Nat → Byte}
    (hn : 16 * n < 2 ^ 64) (hkc : k + c ≤ n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ i < 16 * c, v i = (F (k + i / 16)).getD (i % 16) 0) :
    EcbInv m₀ (patch m (D + BitVec.ofNat 64 (16 * k)) (16 * c) v) D n (k + c) F := by
  intro i hi
  by_cases h1 : 16 * k ≤ i ∧ i < 16 * (k + c)
  · rw [ite_eq_left h1.2]
    have e : D + BitVec.ofNat 64 i = D + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 (i - 16 * k) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h1.1]
    rw [e, patch_at (by omega_using [h1]) (by omega_using [hn, hkc]), hv _ (by omega_using [h1]),
      show k + (i - 16 * k) / 16 = i / 16 by omega_using [h1], show (i - 16 * k) % 16 = i % 16 by omega_using [h1]]
  · rw [patch_frame _ _ _ _ _ (fun r hr hc => ?_), h i hi]
    · by_cases h2 : i < 16 * k
      · rw [ite_eq_left h2, ite_eq_left (by omega_using [h2])]
      · rw [ite_eq_right h2, ite_eq_right (by omega_using [h1, h2])]
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc
      have hk' : 16 * k < 2 ^ 64 := by omega_using [hkc, hn]
      have hi64 : i < 2 ^ 64 := by omega_using [hi, hn]
      have e : D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 (16 * k)) = BitVec.ofNat 64 i - BitVec.ofNat 64 (16 * k) := by
        bv_omega
      rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hi64] at hc
      omega_using [hc, h1, hi, hn, hkc]

/-- The data after the last block, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  obtain hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

/-- The block `j` that the data ends with. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

/-- What a transformation of eight blocks does: `f R w` to each, with the round keys as `KeysAt` has them. -/
def CryptOk (crypt8 : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {rd wr : List Region} {B S E : BitVec 32} {R : Nat} {w : List Byte}, Env rd wr B S E R → ∀ {s₀ : State},
    Good rd wr B S E R w s₀ → KeysAt s₀.mem B w (R - 1) → ∀ {T : Nat → Spec.Aes.State}, InRel (Q s₀) T →
    WP isa crypt8 s₀ fun s => RGood rd wr B S E R w s₀ s ∧ InRel (Q s) (fun b => f R w (T b))

theorem encrypt8_cryptOk : CryptOk encrypt8 Spec.Aes.cipher := fun he _ hg hk _ hin => encrypt8_ok he hg hk hin
theorem decrypt8_cryptOk : CryptOk decrypt8 Spec.Aes.invCipher := fun he _ hg hk _ hin => decrypt8_ok he hg hk hin

/-! ## Where the data is -/

/-- The data, `n` blocks at `D`, apart from what the code keeps. -/
structure Data (wr : List Region) (B S E D : BitVec 32) (n : Nat) : Prop where
  dat : reg32 D (16 * n) ∈ wr
  fit : D.toNat + 16 * n ≤ 2 ^ 32
  sep : (reg32 D (16 * n)).Disjoint (reg32 B 2048)
  sch : (reg32 S 240).Disjoint (reg32 D (16 * n))
  args : ∀ i < 2, Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (reg32 D (16 * n))

/-- What every phase keeps of the entry: the saved registers, and what is
neither working space nor data. -/
structure Kept (B D : BitVec 32) (n : Nat) (m₀ : Mem) (g : Reg → BitVec 32) (m : Mem) : Prop where
  saved : Spill.Saved m (addr B) g savedRegs
  frame : Frame [reg32 B 2048, reg32 D (16 * n)] m₀ m

section
variable {rd wr : List Region} {B S E D : BitVec 32} {R n : Nat} {w : List Byte} {m₀ : Mem} {g : Reg → BitVec 32}

/-- The saved registers' region. -/
theorem saved_in (hfit : B.toNat + 2048 ≤ 2 ^ 32) :
    ∀ p ∈ savedRegs, (⟨addr B 272, 16⟩ : Region).Contains (addr B p.2) 4 := fun p hp => by
  have : 272 ≤ p.2 ∧ p.2 + 4 ≤ 288 := by revert p hp; decide
  exact part_contains hfit (by decide) this.1 this.2 (by decide)

/-- A write of working space but the saved registers. -/
theorem Kept.scratch (hfit : B.toNat + 2048 ≤ 2 ^ 32) {m m' : Mem} (h : Kept B D n m₀ g m) {rs : List Region}
    (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r (reg32 B 2048))
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr B 272, 16⟩ r) : Kept B D n m₀ g m' where
  saved := h.saved.of_frame hf (saved_in hfit) hd
  frame := h.frame.trans (hf.sub fun r hr => ⟨reg32 B 2048, by simp, hs r hr⟩)

/-- A write of data. -/
theorem Kept.data (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hsep : (reg32 D (16 * n)).Disjoint (reg32 B 2048)) {m m' : Mem}
    (h : Kept B D n m₀ g m) {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (reg32 D (16 * n))) : Kept B D n m₀ g m' where
  saved := h.saved.of_frame hf (saved_in hfit) fun r hr =>
    ((hsep.sub_right (part_sub_reg hfit (by decide))).symm).sub_right (hs r hr)
  frame := h.frame.trans (hf.sub fun r hr => ⟨reg32 D (16 * n), by simp, hs r hr⟩)

/-- A write of the slots. -/
theorem Kept.slots (hfit : B.toNat + 2048 ≤ 2 ^ 32) {m m' : Mem} (h : Kept B D n m₀ g m)
    (hf : Frame [reg32 B 272] m m') : Kept B D n m₀ g m' :=
  h.scratch hfit hf slots_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨B.setWidth 64, 272⟩
    rw [← addr_zero]
    exact part_disj hfit (by decide) (by decide) (.inr (by decide))

/-- A write of data keeps what `Good` says. -/
theorem Good.data (hd : Data wr B S E D n) (he : Env rd wr B S E R) {s s' : State} (hg : Good rd wr B S E R w s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hdi : s'.gpr .edi = s.gpr .edi) (hsp : s'.gpr .esp = s.gpr .esp)
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, Region.Sub r (reg32 D (16 * n))) :
    Good rd wr B S E R w s' where
  rd := hrd.trans hg.rd
  wr := hwr.trans hg.wr
  edi := hdi.trans hg.edi
  esp := hsp.trans hg.esp
  arg0 := by
    rw [← hg.arg0]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (hd.args 0 (by decide)).sub_right (hs r hr)) (by decide)
  arg1 := by
    rw [← hg.arg1]
    exact hf.readW (Region.contains_self _ _) (fun r hr => (hd.args 1 (by decide)).sub_right (hs r hr)) (by decide)
  w := fun i hi => by
    rw [← hg.w i hi]
    have := he.hR
    exact hf _ fun r hr hc => hd.sch _ (reg_contains he.fitS (by omega_using [hi, this]) (by decide)) (hs r hr _ hc)

theorem KeysAt.data (hd : Data wr B S E D n) (hfit : B.toNat + 2048 ≤ 2 ^ 32) {m m' : Mem} {k : Nat} (hk : k ≤ 13)
    (h : KeysAt m B w k) {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (reg32 D (16 * n))) : KeysAt m' B w k :=
  h.frame hk hfit hf fun r hr => ((hd.sep.sub_right (part_sub_reg hfit (by decide))).symm).sub_right (hs r hr)

/-- Part of a buffer, from block `k` on. -/
theorem part_blocks {A : BitVec 32} {k m : Nat} (hfit : A.toNat + 16 * n ≤ 2 ^ 32) (h : k + m ≤ n) (hm : 0 < m) :
    (A + BitVec.ofNat 32 (16 * k)).toNat + 16 * m ≤ 2 ^ 32 ∧
      (A + BitVec.ofNat 32 (16 * k)).setWidth 64 = A.setWidth 64 + BitVec.ofNat 64 (16 * k) ∧
      Region.Sub ⟨(A + BitVec.ofNat 32 (16 * k)).setWidth 64, 16 * m⟩ (reg32 A (16 * n)) := by
  refine ⟨?_, ptr_lt (m := n) hfit (by omega_using [h, hm]), ?_⟩
  · rw [Straight.toNat_add_off (by omega_using [hfit, h, hm])]; omega_using [hfit, h]
  · rw [← addr_zero, addr_add, Nat.add_zero]
    exact part_sub_reg hfit (by omega_using [h])

/-- Before a pass, `k` blocks done. -/
structure BInv (rd wr : List Region) (B S E D : BitVec 32) (R n : Nat) (w : List Byte) (m₀ : Mem)
    (g : Reg → BitVec 32) (F : Nat → Spec.Aes.State) (k : Nat) (s : State) : Prop where
  hk : k ≤ n
  good : Good rd wr B S E R w s
  keys : KeysAt s.mem B w (R - 1)
  kept : Kept B D n m₀ g s.mem
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 (16 * k)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (n - k)
  data : EcbInv m₀ s.mem (D.setWidth 64) n k F

theorem copyIn_ok (he : Env rd wr B S E R) (hd : Data wr B S E D n) {F : Nat → Spec.Aes.State} {k : Nat} {s : State}
    (hi : BInv rd wr B S E D R n w m₀ g F k s) (hk : k < n) :
    WP isa copyIn s fun s' => BInv rd wr B S E D R n w m₀ g F k s' ∧
      ∀ i < 16 * min 8 (n - k), s'.mem (B.setWidth 64 + BitVec.ofNat 64 i) =
        m₀ (D.setWidth 64 + BitVec.ofNat 64 (16 * k + i)) := by
  have fD := hd.fit
  have fB := he.fitB
  have hR := he.hR
  obtain ⟨m, hm⟩ : ∃ m, m = min 8 (n - k) := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 < m := by omega_using [hm, hk]
  have hm8 : m ≤ 8 := by omega_using [hm]
  have hkm : k + m ≤ n := by omega_using [hm, hk]
  obtain ⟨pfit, paddr, psub⟩ := part_blocks fD hkm hm0
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have hbp₂ : s₂.gpr .ebp = BitVec.ofNat 32 (n - k) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hi.ebp]
  refine WP.seq (takeCount_ok (by omega_using [fD]) hbp₂ fun s₃ u₃ => ?_)
  rw [← hm] at u₃
  have hsi : s₃.gpr .esi = D + BitVec.ofNat 32 (16 * k) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.ebx]
  have hdx : s₃.gpr .edx = B := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.good.edi]
  have hmem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h1, u₂.other r h2, u₁.other r h3]
  have rd₃ : s₃.rd = rd := by rw [u₃.rd, u₂.rd, u₁.rd, hi.good.rd]
  have wr₃ : s₃.wr = wr := by rw [u₃.wr, u₂.wr, u₁.wr, hi.good.wr]
  have ssub : Region.Sub ⟨B.setWidth 64, 16 * m⟩ (reg32 B 272) := Region.sub_prefix (by omega_using [hm8])
  have ssub' : Region.Sub ⟨B.setWidth 64, 16 * m⟩ (reg32 B 2048) := Region.sub_prefix (by omega_using [hm8])
  refine WP.mono (copy_loop (src := .esi) (dst := .edx) (by decide) (by decide) (by decide) (by omega_using [hm8]) hm0 u₃.gpr
    (by rw [hsi]; exact pfit) (by rw [hdx]; omega_using [fB, hm8])
    (by rw [hsi, rd₃, wr₃]; exact blocksIn_of (List.mem_append_right _ hd.dat) fD (by omega_using [hkm]))
    (by rw [hdx, wr₃]; have := blocksIn_of (a := 0) (m := m) he.scr fB (by omega_using [hm8]); simpa using this)
    (by rw [hsi, hdx]; exact (hd.sep.sub_left psub).sub_right ssub')) fun s₄ h₄ => ?_
  have hf : Frame [reg32 B 272] s.mem s₄.mem := by
    rw [h₄.mem, hdx, ← hmem₃]
    exact (patch_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, ssub⟩
  have g₄ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [h₄.other r h1 (by simp [h2, h3]), g₃ r h1 h2 h3]
  refine ⟨⟨hi.hk, hi.good.step he (by rw [h₄.rd, rd₃, hi.good.rd]) (by rw [h₄.wr, wr₃, hi.good.wr])
    (g₄ _ (by decide) (by decide) (by decide)) (g₄ _ (by decide) (by decide) (by decide)) hf slots_sub,
    hi.keys.frame (by omega_using [hR]) fB hf (keys_slots fB), hi.kept.slots fB hf,
    by rw [g₄ _ (by decide) (by decide) (by decide), hi.ebx], by rw [g₄ _ (by decide) (by decide) (by decide), hi.ebp],
    ecbInv_frame hf (fun r hr => hd.sep.sub_right (slots_sub r hr)) (by omega_using [fD]) hi.data⟩, fun i hi' => ?_⟩
  rw [h₄.mem, hdx, patch_at hi' (by omega_using [hm8]), hsi, paddr, hmem₃, BitVec.add_assoc, ← BitVec.ofNat_add,
    hi.data _ (by omega_using [hi', hkm]), ite_eq_right (by omega_using [])]

theorem copyOut_ok (he : Env rd wr B S E R) (hd : Data wr B S E D n) {F : Nat → Spec.Aes.State} {k : Nat} {s : State}
    (hi : BInv rd wr B S E D R n w m₀ g F k s) (hk : k < n)
    (hv : ∀ i < 16 * min 8 (n - k), s.mem (B.setWidth 64 + BitVec.ofNat 64 i) = (F (k + i / 16)).getD (i % 16) 0) :
    WP isa copyOut s fun s' => BInv rd wr B S E D R n w m₀ g F (k + min 8 (n - k)) s' ∧
      s'.zf = some (decide (k + min 8 (n - k) = n)) := by
  have fD := hd.fit
  have fB := he.fitB
  have hR := he.hR
  obtain ⟨m, hm⟩ : ∃ m, m = min 8 (n - k) := ⟨_, rfl⟩
  rw [← hm] at hv ⊢
  have hm0 : 0 < m := by omega_using [hm, hk]
  have hm8 : m ≤ 8 := by omega_using [hm]
  have hkm : k + m ≤ n := by omega_using [hm, hk]
  obtain ⟨pfit, paddr, psub⟩ := part_blocks fD hkm hm0
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have hbp₁ : s₁.gpr .ebp = BitVec.ofNat 32 (n - k) := by rw [u₁.other _ (by decide), hi.ebp]
  refine WP.seq (takeCount_ok (by omega_using [fD]) hbp₁ fun s₂ u₂ => ?_)
  rw [← hm] at u₂
  refine WP.seq (wp_sub fun s₃ u₃ _ => WP.block_nil ?_)
  have hcx : s₃.gpr .ecx = BitVec.ofNat 32 m := by rw [u₃.other _ (by decide), u₂.gpr]
  have hbp : s₃.gpr .ebp = BitVec.ofNat 32 (n - (k + m)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), hbp₁, Wp.sub_ofNat (by omega_using [hkm]),
      show n - k - m = n - (k + m) by omega_using []]
  have hbx : s₃.gpr .ebx = D + BitVec.ofNat 32 (16 * k) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hi.ebx]
  have hdx : s₃.gpr .edx = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.good.edi]
  have hmem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h1, u₁.other r h2]
  have rd₃ : s₃.rd = rd := by rw [u₃.rd, u₂.rd, u₁.rd, hi.good.rd]
  have wr₃ : s₃.wr = wr := by rw [u₃.wr, u₂.wr, u₁.wr, hi.good.wr]
  have ssub : Region.Sub ⟨B.setWidth 64, 16 * m⟩ (reg32 B 272) := Region.sub_prefix (by omega_using [hm8])
  have ssub' : Region.Sub ⟨B.setWidth 64, 16 * m⟩ (reg32 B 2048) := Region.sub_prefix (by omega_using [hm8])
  refine WP.seq (WP.mono (copy_loop (src := .edx) (dst := .ebx) (by decide) (by decide) (by decide) (by omega_using [hm8])
    hm0 hcx (by rw [hdx]; omega_using [fB, hm8]) (by rw [hbx]; exact pfit)
    (by rw [hdx, rd₃, wr₃]; have := blocksIn_of (a := 0) (m := m) (List.mem_append_right rd he.scr) fB (by omega_using [hm8])
        simpa using this)
    (by rw [hbx, wr₃]; exact blocksIn_of hd.dat fD (by omega_using [hkm]))
    (by rw [hbx, hdx]; exact ((hd.sep.sub_left psub).sub_right ssub').symm)) fun s₄ h₄ => ?_)
  refine wp_test fun s₅ u₅ hz => WP.block_nil ?_
  have hmem₅ : s₅.mem = patch s.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * k)) (16 * m)
      (fun i => s.mem (B.setWidth 64 + BitVec.ofNat 64 i)) := by
    rw [u₅.mem, h₄.mem, hbx, hdx, paddr, hmem₃]
  have hf : Frame [⟨(D + BitVec.ofNat 32 (16 * k)).setWidth 64, 16 * m⟩] s.mem s₅.mem := by
    rw [hmem₅, paddr]; exact patch_frame _ _ _ _
  have hsub : ∀ r ∈ [(⟨(D + BitVec.ofNat 32 (16 * k)).setWidth 64, 16 * m⟩ : Region)],
      Region.Sub r (reg32 D (16 * n)) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact psub
  have g₅ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .ebp → r ≠ .ebx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.gpr, h₄.other r h1 (by simp [h2, h4]), g₃ r h1 h2 h3]
  have hbp₅ : s₅.gpr .ebp = BitVec.ofNat 32 (n - (k + m)) := by
    rw [u₅.gpr, h₄.other _ (by decide) (by decide), hbp]
  refine ⟨⟨hkm, hi.good.data hd he (by rw [u₅.rd, h₄.rd, rd₃, hi.good.rd]) (by rw [u₅.wr, h₄.wr, wr₃, hi.good.wr])
    (g₅ _ (by decide) (by decide) (by decide) (by decide)) (g₅ _ (by decide) (by decide) (by decide) (by decide)) hf hsub,
    KeysAt.data hd fB (by omega_using [hR]) hi.keys hf hsub, hi.kept.data fB hd.sep hf hsub, ?_, hbp₅, ?_⟩, ?_⟩
  · rw [u₅.gpr, h₄.ptr _ (by simp), hbx, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  · rw [hmem₅]; exact ecbInv_patch (by omega_using [fD]) hkm hi.data hv
  · rw [hz, h₄.other _ (by decide) (by decide), hbp, BitVec.and_self, ofNat_beq_zero (by omega_using [fD])]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hkm], fun h => by omega_using [h]⟩)

/-- The states of the slots. -/
theorem stateAt_getD (m : Mem) (A : Addr) (b : Nat) {t : Nat} (ht : t < 16) :
    (Spec.Aes.stateAt m (A + BitVec.ofNat 64 (16 * b))).getD t 0 = m (A + BitVec.ofNat 64 (16 * b + t)) := by
  rw [getD_eq _ ht]
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem stateAt_eq {m m' : Mem} {A A' : Addr} {b c : Nat}
    (h : ∀ t < 16, m (A + BitVec.ofNat 64 (16 * b + t)) = m' (A' + BitVec.ofNat 64 (16 * c + t))) :
    Spec.Aes.stateAt m (A + BitVec.ofNat 64 (16 * b)) = Spec.Aes.stateAt m' (A' + BitVec.ofNat 64 (16 * c)) := by
  apply Vector.ext
  intro t ht
  rw [← getD_eq _ ht, ← getD_eq _ ht, stateAt_getD _ _ _ ht, stateAt_getD _ _ _ ht, h t ht]

/-- A pass. -/
theorem blockGroup_ok {crypt8 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt8 f) (he : Env rd wr B S E R) (hd : Data wr B S E D n) {k : Nat} {s : State}
    (hi : BInv rd wr B S E D R n w m₀ g (ecbOut f m₀ (D.setWidth 64) R w) k s) (hk : k < n) :
    WP isa (blockGroup crypt8) s fun s' =>
      BInv rd wr B S E D R n w m₀ g (ecbOut f m₀ (D.setWidth 64) R w) (k + min 8 (n - k)) s' ∧
      s'.zf = some (decide (k + min 8 (n - k) = n)) := by
  have fD := hd.fit
  have fB := he.fitB
  refine WP.seq (WP.mono (copyIn_ok he hd hi hk) fun s₁ ⟨h₁, hin⟩ => ?_)
  -- The blocks in the slots.
  have hrel : InRel (Q s₁) fun b => Spec.Aes.stateAt s₁.mem (B.setWidth 64 + BitVec.ofNat 64 (16 * b)) :=
    inRel_of_bytes h₁.good.edi fB fun i _ => by
      rw [stateAt_getD _ _ _ (Nat.mod_lt _ (by decide)), Nat.div_add_mod]
  refine WP.seq (WP.mono (hcr he h₁.good h₁.keys hrel) fun s₂ ⟨r₂, hout⟩ => ?_)
  refine copyOut_ok he hd ⟨h₁.hk, r₂.good, r₂.keys, h₁.kept.slots fB r₂.frame,
    (r₂.keep _ (by decide) (by decide) (by decide)).trans h₁.ebx,
    (r₂.keep _ (by decide) (by decide) (by decide)).trans h₁.ebp,
    ecbInv_frame r₂.frame (fun r hr => hd.sep.sub_right (slots_sub r hr)) (by omega_using [fD]) h₁.data⟩ hk fun i hi' => ?_
  rw [bytes_of_inRel r₂.good.edi fB hout i (by omega_using [hi'])]
  refine congrArg (fun x : Spec.Aes.State => (f R w x).getD (i % 16) 0) (stateAt_eq fun t ht => ?_)
  rw [hin _ (by omega_using [hi', ht]), show 16 * (k + i / 16) + t = 16 * k + (16 * (i / 16) + t) by omega_using []]

/-- The passes. -/
theorem blockGroups_ok {crypt8 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt8 f) (he : Env rd wr B S E R) (hd : Data wr B S E D n) {s : State}
    (hi : BInv rd wr B S E D R n w m₀ g (ecbOut f m₀ (D.setWidth 64) R w) 0 s) (hn : 0 < n) :
    WP isa (.loop (blockGroup crypt8) .ne) s
      (BInv rd wr B S E D R n w m₀ g (ecbOut f m₀ (D.setWidth 64) R w) n) := by
  refine WP.loop (M := isa) (fun j s => ∃ k, j = n - k ∧ k < n ∧
      BInv rd wr B S E D R n w m₀ g (ecbOut f m₀ (D.setWidth 64) R w) k s)
    (fun j s ⟨k, hj, hk, hi⟩ => WP.mono (blockGroup_ok hcr he hd hi hk) fun s' ⟨h, hz⟩ => ?_) n s ⟨0, rfl, hn, hi⟩
  by_cases hlast : k + min 8 (n - k) = n
  · rw [hlast] at h
    exact .inl ⟨by simp [X86.eval, hz, hlast], h⟩
  · exact .inr ⟨by simp [X86.eval, hz, hlast], n - (k + min 8 (n - k)), by omega_using [hj, hk], _, rfl,
      by omega_using [hlast, hk], h⟩

end

/-! ## The prologue and the epilogue -/

/-- The saved registers are in working space. -/
theorem saved_reg {B : BitVec 32} (hfit : B.toNat + 2048 ≤ 2 ^ 32) (p : Reg × Nat) (hp : p ∈ savedRegs) :
    (reg32 B 2048).Contains (addr B p.2) 4 :=
  reg_contains hfit (by have : p.2 + 4 ≤ 2048 := by revert p hp; decide
                        exact this) (by decide)

/-- After `saveRegs k`. -/
structure Entered (B : BitVec 32) (s₀ s : State) : Prop where
  edi : s.gpr .edi = B
  other : ∀ r, r ≠ .eax → r ≠ .edi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr B 272, 16⟩] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr B) s₀.gpr savedRegs

theorem saveRegs_ok {k : Nat} {s : State} {B : BitVec 32} (hB : s.mem.readW (addr (s.gpr .esp) (4 + 4 * k)) 32 = B)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * k)) 4) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    (hw : reg32 B 2048 ∈ s.wr) : WP isa (.block (saveRegs k)) s (Entered B s) := by
  show WP isa (.block (.mov .eax (.mem (argOp k)) :: (Spill.saveCode .eax savedRegs ++ [movR .edi .eax]))) s _
  refine wp_ldm (B := s.gpr .esp) (o := 4 + 4 * k) rfl hin fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := u₁.gpr.trans hB
  refine Spill.save_ok savedRegs (fun p hp => ?_) fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  · rw [e₁, u₁.wr]
    exact ⟨_, hw, saved_reg hfit p hp⟩
  have m₃ : s₃.mem = Spill.saveMem s.mem (addr B) s₁.gpr savedRegs := by rw [u₃.mem, u₂.mem, e₁, u₁.mem]
  have hs : Spill.Saved s₃.mem (addr B) s₁.gpr savedRegs := by
    rw [m₃]; exact Spill.saveMem_saved_addr _ _ (n := 2048) (by decide) hfit
  refine ⟨by rw [u₃.gpr, u₂.gpr, e₁], fun r h1 h2 => by rw [u₃.other r h2, u₂.gpr, u₁.other r h1],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], ?_, fun p hp => ?_⟩
  · rw [m₃]; exact Spill.saveMem_frame (List.mem_singleton_self _) _ _ _ _ (saved_in hfit)
  · rw [hs p hp, u₁.other _ (by revert p hp; decide)]

theorem restoreRegs_ok {s : State} {B : BitVec 32} {g : Reg → BitVec 32} (hb : s.gpr .edi = B)
    (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hw : reg32 B 2048 ∈ s.wr) (hs : Spill.Saved s.mem (addr B) g savedRegs) :
    WP isa (.block restoreRegs) s fun s' =>
      Spill.Restored s s' g ([(.ebx, 272), (.esi, 276), (.ebp, 284)] ++ [(.edi, 280)]) := by
  have hm : ∀ p ∈ ([(.ebx, 272), (.esi, 276), (.ebp, 284)] ++ [(.edi, 280)] : List (Reg × Nat)), p ∈ savedRegs := by
    decide
  subst hb
  refine Spill.restoreBase_ok (b := .edi) (d := 280) (rest := []) [(.ebx, 272), (.esi, 276), (.ebp, 284)] (by decide)
    (fun p hp => ?_) (hs.sub hm) fun s' r => WP.block_nil r
  exact ⟨_, List.mem_append_right _ hw, saved_reg hfit p (hm p hp)⟩

/-! ## The whole function -/

theorem arg_read (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

theorem correct_blocks {crypt8 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt8 f) {s₀ : State} (hp : BPre s₀) :
    WP isa (blocks crypt8) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 f).post s₀ s' := by
  obtain ⟨B, hB⟩ : ∃ B, B = bScrP s₀ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = bDatP s₀ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = bSchP s₀ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = s₀.gpr .esp := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = bRounds s₀ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = bN s₀ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.Aes.bytesAt s₀.mem (S.setWidth 64) (16 * (R + 1)) := ⟨_, rfl⟩
  have fB : B.toNat + 2048 ≤ 2 ^ 32 := by rw [hB]; exact hp.fB
  have fD : D.toNat + 16 * n ≤ 2 ^ 32 := by rw [hD, hn]; exact hp.fD
  have fS : S.toNat + 240 ≤ 2 ^ 32 := by rw [hS]; exact hp.fS
  have fE : E.toNat + 24 ≤ 2 ^ 32 := by rw [hE]; exact hp.fSp
  have argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr (s₀.gpr .esp) 4, 20⟩ : Region).Contains _ _
    rw [← hE]
    exact part_contains (N := 24) fE (by omega_using []) (by omega_using [hi]) (by omega_using [hi]) (by decide)
  have argSub : ∀ i < 5, Region.Sub ⟨addr E (4 + 4 * i), 4⟩ (bArgR s₀) := fun i hi => by
    show Region.Sub _ (⟨addr (s₀.gpr .esp) 4, 20⟩ : Region)
    rw [← hE]
    exact part_sub (N := 24) (b := E) fE (by omega_using []) (by omega_using []) (by omega_using [hi])
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr, hB]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hwD : reg32 D (16 * n) ∈ s₀.wr := by rw [hp.wr, hD, hn]; exact List.mem_cons_self ..
  have hrS : reg32 S 240 ∈ s₀.rd := by rw [hp.rd, hS]; exact List.mem_cons_self ..
  have hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argIn : ∀ i < 5, InRegions (s₀.rd ++ s₀.wr) (addr E (4 + 4 * i)) 4 := fun i hi =>
    ⟨bArgR s₀, List.mem_append_left _ hrA, argC i hi⟩
  have aB : (bArgR s₀).Disjoint (reg32 B 2048) := by rw [hB]; exact hp.aB
  have aD : (bArgR s₀).Disjoint (reg32 D (16 * n)) := by rw [hD, hn]; exact hp.aD
  have he : Env s₀.rd s₀.wr B S E R :=
    { scr := hwB
      fitB := fB
      sch := List.mem_append_left _ hrS
      fitS := fS
      sepS := by rw [hS, hB]; exact hp.dSB
      rounds := by rw [hR]; exact hp.rounds
      argIn := fun i hi => argIn i (by omega_using [hi])
      argSep := fun i hi => aB.sub_left (argSub i (by omega_using [hi])) }
  have hd : Data s₀.wr B S E D n :=
    { dat := hwD
      fit := fD
      sep := by rw [hD, hn, hB]; exact hp.dDB
      sch := by rw [hS, hD, hn]; exact hp.dSD
      args := fun i hi => aD.sub_left (argSub i (by omega_using [hi])) }
  have hg₀ : ∀ i < 16 * (R + 1), s₀.mem (addr S i) = w.getD i 0 := fun i hi => by
    have := he.hR
    rw [hw, addr_eq (by omega_using [fS, hi, this])]
    simp only [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
  unfold blocks
  refine WP.seq (WP.mono (saveRegs_ok (by rw [hB]; rfl) (hE ▸ argIn 4 (by decide)) fB hwB) fun s₁ h₁ => ?_)
  have sub₁ : ∀ r ∈ [(⟨addr B 272, 16⟩ : Region)], Region.Sub r (reg32 B 2048) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)
  have good₁ : Good s₀.rd s₀.wr B S E R w s₁ :=
    { rd := h₁.rd
      wr := h₁.wr
      edi := h₁.edi
      esp := (h₁.other _ (by decide) (by decide)).trans hE.symm
      arg0 := by
        rw [h₁.frame.readW (argC 0 (by decide)) (fun r hr => aB.sub_right (sub₁ r hr)) (by decide), hE, hS]; rfl
      arg1 := by
        rw [h₁.frame.readW (argC 1 (by decide)) (fun r hr => aB.sub_right (sub₁ r hr)) (by decide), hE, hR,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
      w := fun i hi => by
        rw [← hg₀ i hi]
        have := he.hR
        exact h₁.frame _ fun r hr hc => he.sepS _ (reg_contains fS (by omega_using [hi, this]) (by decide)) (sub₁ r hr _ hc) }
  refine WP.seq (WP.mono (keys_ok he good₁) fun s₂ ⟨good₂, f₂, keys₂⟩ => ?_)
  have sub₂ : ∀ r ∈ [(⟨addr B keysOff, 1664⟩ : Region)], Region.Sub r (reg32 B 2048) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)
  have kept₂ : Kept B D n s₀.mem s₀.gpr s₂.mem :=
    Kept.scratch fB ⟨h₁.saved, h₁.frame.sub fun r hr => ⟨_, List.mem_cons_self .., sub₁ r hr⟩⟩ f₂ sub₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj fB (by decide) (by decide) (.inl (by decide))
  have F₂ : Frame [reg32 B 2048] s₀.mem s₂.mem :=
    (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, sub₁ r hr⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, sub₂ r hr⟩)
  have arg₂ : ∀ i < 5, s₂.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [F₂.readW (argC i hi) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact aB) (by decide), hE]; rfl
  have data₂ : EcbInv s₀.mem s₂.mem (D.setWidth 64) n 0 (ecbOut f s₀.mem (D.setWidth 64) R w) := fun i hi => by
    rw [ite_eq_right (show ¬ i < 16 * 0 by omega_using [])]
    exact F₂.bytes (R := reg32 D (16 * n)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.sep) (by show 16 * n ≤ 2 ^ 64; omega_using [fD]) hi
  -- Between the loops.
  refine WP.seq (wp_ldm (B := E) (o := 12) good₂.esp (by rw [good₂.rd, good₂.wr]; exact argIn 2 (by decide))
    fun s₃ u₃ => wp_ldm (B := E) (o := 16) ((u₃.other _ (by decide)).trans good₂.esp)
      (by rw [u₃.rd, u₃.wr, good₂.rd, good₂.wr]; exact argIn 3 (by decide)) fun s₄ u₄ => wp_test fun s₅ u₅ hz =>
      WP.block_nil ?_)
  have hbx : s₅.gpr .ebx = D := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, arg₂ 2 (by decide), hD]
  have hbp : s₅.gpr .ebp = BitVec.ofNat 32 n := by
    rw [u₅.gpr, u₄.gpr, u₃.mem, arg₂ 3 (by decide), hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have hz₅ : s₅.zf = some (decide (n = 0)) := by
    rw [hz, ← u₅.gpr, hbp, BitVec.and_self, ofNat_beq_zero (by omega_using [fD])]
  have i₅ : BInv s₀.rd s₀.wr B S E D R n w s₀.mem s₀.gpr (ecbOut f s₀.mem (D.setWidth 64) R w) 0 s₅ :=
    { hk := Nat.zero_le _
      good := (good₂.upd he u₃ (by decide) (by decide) |>.upd he u₄ (by decide) (by decide)).step he (rs := []) u₅.rd u₅.wr
        (by rw [u₅.gpr]) (by rw [u₅.gpr]) (by rw [u₅.mem]; exact Frame.refl _ _) (by simp)
      keys := by rw [m₅]; exact keys₂
      kept := by rw [m₅]; exact kept₂
      ebx := by rw [hbx]; simp
      ebp := hbp
      data := by rw [m₅]; exact data₂ }
  refine WP.seq (WP.mono (Q := BInv s₀.rd s₀.wr B S E D R n w s₀.mem s₀.gpr (ecbOut f s₀.mem (D.setWidth 64) R w) n)
    (WP.ite (decide (n = 0)) (by simp only [X86.eval, hz₅]) (fun hb => WP.block_nil ?_) fun hb => ?_) fun s₆ h₆ => ?_)
  · have hn0 : n = 0 := by simpa using hb
    have := i₅
    rw [hn0] at this ⊢
    exact this
  · exact blockGroups_ok hcr he hd i₅ (Nat.pos_of_ne_zero (by simpa using hb))
  -- The epilogue.
  refine WP.mono (restoreRegs_ok h₆.good.edi fB (by rw [h₆.good.wr]; exact hwB) h₆.kept.saved) fun s₇ r₇ => ⟨⟨?_, ?_⟩, ?_⟩
  · exact r₇.abi (by decide) (by decide) (h₆.good.esp.trans hE)
  · rw [r₇.mem]
    refine h₆.kept.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hB]; exact hp.rB
    · rw [hD, hn]; exact hp.rD
  · show Spec.Aes.statesAt s₇.mem ((bDatP s₀).setWidth 64) (bN s₀) = _
    rw [r₇.mem, ← hD, ← hn, statesAt_of_ecbInv h₆.data]
    simp only [Spec.Aes.statesAt, List.map_map, hD, hn, hw, hS, hR]
    rfl

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  (correct_blocks encrypt8_cryptOk (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  (correct_blocks decrypt8_cryptOk (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub encryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub decryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Aes.X86.Sse
