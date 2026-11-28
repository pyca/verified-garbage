module

-- separate module: the lanes' addresses, one stage of the chain of verify's proof

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopIdx
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
public import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGenPro

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the lanes' addresses

Untrusted: everything here is checked by Lean. `treeLanes` with the layer
`L` in `r10` and the tree `T` in `r9` writes `layerTree L T` to every
lane's address (`treeG_ok`), as key generation's `tree_ok` does for the tree 0.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR)
open VG.Impl.SlhDsa.X86_64.Shake (treeLanes)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (in_scr disj_scr)
open VG.Proof.SlhDsa.X86_64.KeyGen (lane lane_lt lane_disj seed_adrs_disj bytesAt_split lanesR wp_flatMap)

theorem bswap_bytes8 {T : Nat} (_hT : T < 2 ^ 64) :
    ((List.range (64 / 8)).map fun d => (bswap64 (BitVec.ofNat 64 T)).extractLsb' (8 * d) 8) = toByte T 8 := by
  simp only [toByte, show 64 / 8 = 8 from rfl]
  refine List.map_congr_left fun d hd => ?_
  have hd' := List.mem_range.mp hd
  rw [Proof.Bignum.X86_64.WordIO.bswap_byte _ hd', Proof.Bignum.X86_64.WordIO.extract_nat _ (by omega)]

theorem toByte_12 {T : Nat} (hT : T < 2 ^ 64) : toByte T 12 = toByte 0 4 ++ toByte T 8 := by
  simp only [toByte, show (12 : Nat) = 4 + 8 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have : T / 256 ^ (4 + 8 - 1 - i) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hT (by
      rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]; exact Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [this, Nat.zero_div]

theorem layerTreeG_eq {L T : Nat} (hT : T < 2 ^ 64) :
    Proof.SlhDsa.layerTree L T = toByte L 4 ++ (toByte 0 4 ++ toByte T 8) := by
  simp only [Proof.SlhDsa.layerTree, toByte_12 hT]

/-- After `j` of the eight addresses of `treeLanes`. -/
def TreeG (n : Nat) (a16 : List Byte) (s : State) (S : Addr) (j : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ k < 4, ∀ b < 2, 2 * k + b < j → bytesAt t.mem (at' S (lane k b + n)) 16 = a16) ∧
    (∀ k < 4, ∀ b < 2, bytesAt t.mem (at' S (lane k b)) n = bytesAt s.mem (at' S (lane k b)) n) ∧
    Frame [lanesR S] s.mem t.mem

theorem itemG_ok {p : Params} (hn : p.n ≤ 32) {L T : Nat} (hL : L < 2 ^ 32) (hT : T < 2 ^ 64) {s : State} {S : Addr}
    (hb : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (h10 : (s.gpr .r10).toNat = L)
    (h11 : s.gpr .r11 = bswap64 (BitVec.ofNat 64 T)) {k b : Nat} (hk : k < 4) (hb2 : b < 2) {t : State} (ht : TreeG p.n (Proof.SlhDsa.layerTree L T) s S (2 * k + b) t) :
    WP isa (.block (setFieldR .rbx (lane k b + p.n) .r10 ++ setField .rbx (lane k b + p.n + 4) 0 ++
      ([.store (Impl.Sha3.X86_64.at_ .rbx (lane k b + p.n + 8)) .r11] : List Instr))) t
      (TreeG p.n (Proof.SlhDsa.layerTree L T) s S (2 * k + b + 1)) := by
  obtain ⟨hg, rd, w, ad, sd, f⟩ := ht
  have eA : Layout.oA = 3296 := rfl
  have hl := lane_lt (b := b) hk
  have hbt : t.gpr .rbx = S := by rw [hg _ (by decide), hb]
  have hwt : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [w]; exact hw
  rw [List.append_assoc]
  refine setFieldR_ok (by decide) (by rw [hg _ (by decide), h10]; exact hL)
    (by rw [hbt]; exact in_scr hwt (by omega)) fun u₁ p₁ => ?_
  refine setField_ok (by decide) (by decide) (by rw [p₁.gpr _ (by decide), hbt, p₁.wr]; exact in_scr hwt (by omega))
    fun u₂ p₂ => ?_
  have hb₂ : u₂.gpr .rbx = S := by rw [p₂.gpr _ (by decide), p₁.gpr _ (by decide), hbt]
  refine wp_store (a := at' S (lane k b + p.n + 8)) (by rw [ea_at, hb₂])
    (by rw [p₂.wr, p₁.wr]; exact in_scr hwt (by omega)) fun u₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
  rw [hbt, hg _ (by decide), h10] at p₁
  rw [p₁.gpr _ (by decide), hbt] at p₂
  have h11' : u₂.gpr .r11 = bswap64 (BitVec.ofNat 64 T) := by rw [p₂.gpr _ (by decide), p₁.gpr _ (by decide), hg _ (by decide), h11]
  -- the three fields
  have e₃ : bytesAt u₃.mem (at' S (lane k b + p.n + 8)) 8 = toByte T 8 := by
    rw [m₃, h11', show (8 : Nat) = 64 / 8 from rfl, bytesAt_writeW _ (by decide) (by decide), bswap_bytes8 hT]
  have e₂ : bytesAt u₃.mem (at' S (lane k b + p.n + 4)) 4 = toByte 0 4 := by
    rw [m₃, ← p₂.bytes]
    exact bytesAt_frame (frame_writeW _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by omega) (by omega)) (by omega)
  have e₁ : bytesAt u₃.mem (at' S (lane k b + p.n)) 4 = toByte L 4 := by
    rw [m₃, ← p₁.bytes, bytesAt_frame (frame_writeW _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by omega) (by omega)) (by omega)]
    exact bytesAt_frame p₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by omega) (by omega)) (by omega)
  have hF : Frame [⟨at' S (lane k b + p.n), 16⟩] t.mem u₃.mem := by
    rw [m₃]
    refine ((p₁.frame.sub fun r hr => ?_).trans (p₂.frame.sub fun r hr => ?_)).trans
      ((frame_writeW _ _ _).sub fun r hr => ?_) <;> simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
  refine ⟨fun g h => by rw [g₃, p₂.gpr _ h, p₁.gpr _ h, hg _ h], by rw [r₃, p₂.rd, p₁.rd, rd],
    by rw [w₃, p₂.wr, p₁.wr, w], fun k' hk' b' hb' hj => ?_, fun k' hk' b' hb' => ?_, ?_⟩
  · by_cases e : k' = k ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := e
      rw [show (16 : Nat) = 4 + (4 + 8) from rfl, bytesAt_split, bytesAt_split, layerTreeG_eq hT,
        show lane k' b' + p.n + 4 + 4 = lane k' b' + p.n + 8 by omega, e₁, e₂, e₃]
    · rw [bytesAt_frame hF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := lane_disj (S := S) (i := 0) (j := 0) (l := 16) (l' := 16) hn hk' hk hb' hb2
          (by omega) (by omega) (by omega)
        simpa using this) (by omega)]
      exact ad k' hk' b' hb' (by omega)
  · rw [bytesAt_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact seed_adrs_disj hn hk hk') (by omega)]
    exact sd k' hk' b' hb'
  · exact f.trans (hF.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩)

theorem treeG_ok {p : Params} (hn : p.n ≤ 32) {L T : Nat} (hL : L < 2 ^ 32) (hT : T < 2 ^ 64) {s : State} {S : Addr}
    (hb : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (h10 : (s.gpr .r10).toNat = L)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 T) {Q : State → Prop}
    (k : ∀ t u, (∀ g, g ≠ .rax → g ≠ .r11 → u.gpr g = s.gpr g) → TreeG p.n (Proof.SlhDsa.layerTree L T) t S 8 u → t.mem = s.mem →
      t.rd = s.rd → t.wr = s.wr → Q u) :
    WP isa (.block (treeLanes p .r10 .r9)) s Q := by
  unfold treeLanes
  refine wp_mov fun t₁ u₁ => ?_
  refine VG.Proof.Sha3.X86_64.WP.cons rfl ?_
  generalize ht₂ : t₁.setReg .rax (bswap64 (t₁.gpr .rax)) = t₂
  have u₂ : Upd t₁ t₂ .rax (bswap64 (t₁.gpr .rax)) := ht₂ ▸ Upd.setReg _ _ _
  refine wp_mov fun t₃ u₃ => ?_
  have h11 : t₃.gpr .r11 = bswap64 (BitVec.ofNat 64 T) := by rw [u₃.gpr, u₂.gpr, u₁.gpr, h9]
  have hb₃ : t₃.gpr .rbx = S := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb]
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₃.wr := by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw
  have h10₃ : (t₃.gpr .r10).toNat = L := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h10]
  have hm₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (wp_flatMap (P := fun k => TreeG p.n (Proof.SlhDsa.layerTree L T) t₃ S (2 * k)) 4
    ⟨fun _ _ => rfl, rfl, rfl, fun _ _ _ _ h => absurd h (by omega), fun _ _ _ _ => rfl, Frame.refl _ _⟩
    fun k hk t ht => ?_) fun u hu => k t₃ u (fun g h₁ h₂ => ?_) hu hm₃ (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr])
  · refine wp_flatMap (P := fun b => TreeG p.n (Proof.SlhDsa.layerTree L T) t₃ S (2 * k + b)) 2 ht fun b hb2 t' ht' => ?_
    exact itemG_ok hn hL hT hb₃ hw₃ h10₃ h11 hk hb2 ht'
  · rw [hu.1 _ h₁, u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]

end VG.Proof.SlhDsa.X86_64.VerifyTop
