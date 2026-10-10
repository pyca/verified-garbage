import VerifiedGarbage.Proof.Camellia.KeySched

/-!
# Camellia's proofs: what every target uses

Facts about addresses, memory and the specification that the targets'
proofs share: words and bytes (`WordOf`, `bytesAt_words`), copies of
blocks (`writeW_readW_apply`), the data loop's invariant (`DInv`) and its
result (`blocksAt_of_dinv`), the planes of the key schedule's constants
(`sigma_planes`), its values (`kaD_eq`) and its stores
(`schedule_of_stores`). Nothing here depends on a target.
-/

namespace VG.Proof.Camellia

open VG VG.Spec.Camellia
open VG.Impl.Camellia (bytePos keyPlane planeBits sigmas)

/-! ## Addresses -/

theorem addr_add (b : Addr) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := VG.Offset.add_add b x y

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [VG.Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [VG.Offset.add_sub_add_left]; exact VG.Offset.not_lt_sub_ofNat h ht hn he

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega)

/-- A byte of `A`'s area is not among the 8 at `B + e`. -/
theorem not_in_of_disjoint {A B : Addr} {n t e : Nat} (hsep : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) (ht : t < n)
    (he : e + 8 ≤ n) (hn : n < 2 ^ 64) : ¬ (A + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < 8 :=
  fun h => hsep (A + BitVec.ofNat 64 t) (VG.Offset.contains_base A (by omega) (by omega))
    (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))

theorem toNat_off (b : Addr) {d : Nat} (h : b.toNat + d < 2 ^ 64) : (b + BitVec.ofNat 64 d).toNat = b.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem ite_swap2 {α : Type} {k w : Nat} (A B C : α) :
    (if k = w + 1 then A else if k = w then B else C) = if k = w then B else if k = w + 1 then A else C := by
  by_cases h1 : k = w <;> by_cases h2 : k = w + 1 <;> simp [h1, h2]

/-! ## Memory -/

/-- A byte of a little-endian word stored from a load. -/
theorem writeW_readW_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 64) x =
      if (x - a).toNat < 8 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 8) h
  · rfl

/-- A word written inside `R`. -/
theorem frame_writeW {m : Mem} {a : Addr} {R : Region} (v : BitVec 64) (hs : Region.Sub ⟨a, 8⟩ R) :
    Frame [R] m (m.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h => hx R (List.mem_singleton_self _) (hs x (by simp only [Region.Contains]; omega))

/-- A word of a region the frame keeps. -/
theorem wordAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : wordAt m' a = wordAt m a := by
  simp only [wordAt, bytesAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨a, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) (by simpa using hi)

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [blockAt, Vector.getD, hi]

theorem bytesAt_add (m : Mem) (p : Addr) (a n : Nat) :
    bytesAt m p (a + n) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) n := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  refine congrArg (_ ++ ·) (List.map_congr_left fun i _ => ?_)
  show m (p + BitVec.ofNat 64 (a + i)) = m (p + BitVec.ofNat 64 a + BitVec.ofNat 64 i)
  rw [addr_add]

/-- Words stored with their most significant byte first are their `wordBytes`. -/
theorem bytesAt_words (m : Mem) : ∀ (ws : List (BitVec 64)) (p : Addr),
    (∀ i < ws.length, ∀ j < 8, m (p + BitVec.ofNat 64 (8 * i + j)) = byteOf (ws.getD i 0) j) →
    bytesAt m p (8 * ws.length) = ws.flatMap wordBytes
  | [], _, _ => rfl
  | w :: ws, p, h => by
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm, bytesAt_add, List.flatMap_cons]
    have h1 : bytesAt m p 8 = wordBytes w := by
      simp only [bytesAt, wordBytes]
      refine List.map_congr_left fun j hj => ?_
      have := h 0 (by simp) j (List.mem_range.mp hj)
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at this
      exact this
    rw [h1, bytesAt_words m ws _ fun i hi j hj => ?_]
    rw [addr_add, show 8 + (8 * i + j) = 8 * (i + 1) + j by omega]
    have := h (i + 1) (by simp only [List.length_cons]; omega) j hj
    simp only [List.getD_cons_succ] at this
    exact this

/-! ## Words -/

/-- Byte `i` of a word read most significant byte first is the byte at `i`. -/
theorem byteOf_wordAt (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    byteOf (wordAt m a) i = m (a + BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_byteOf _ hi hj, wordAt, getLsbD_ofBytes 64 _ (by omega) (by simp [bytesAt])]
  simp only [bytesAt, List.length_map, List.length_range]
  rw [show 8 - 1 - (56 - 8 * i + j) / 8 = i by omega, show (56 - 8 * i + j) % 8 = j by omega]
  simp [hi]

/-- The subkey's word, little-endian, read as the halves are. -/
theorem wordRel_key (m : Mem) (a : Addr) :
    WordRel (fun _ => m.readW a 64) (fun _ => wordAt m a) := fun _ _ i hi j hj => by
  rw [readW64_bit m a hi hj, byteOf_wordAt m a hi]

/-- The little-endian word `w` holds the bytes of `h`, the most significant first. -/
def WordOf (w h : BitVec 64) : Prop :=
  ∀ i < 8, ∀ j < 8, w.getLsbD (8 * i + j) = (byteOf h i).getLsbD j

theorem WordOf.xor {w x h k : BitVec 64} (hw : WordOf w h) (hx : WordOf x k) : WordOf (w ^^^ x) (h ^^^ k) :=
  fun i hi j hj => by
    rw [BitVec.getLsbD_xor, hw i hi j hj, hx i hi j hj, byteOf_xor, BitVec.getLsbD_xor]

theorem WordOf.congr {w w' h : BitVec 64} (hw : WordOf w h) (he : w' = w) : WordOf w' h := he ▸ hw

theorem WordOf.zero : WordOf 0 0 := fun i hi j hj => by
  rw [getLsbD_byteOf _ hi hj]; simp

theorem WordOf.not {w h : BitVec 64} (hw : WordOf w h) : WordOf (~~~ w) (~~~ h) := fun i hi j hj => by
  rw [getLsbD_byteOf _ hi hj, BitVec.getLsbD_not, BitVec.getLsbD_not, hw i hi j hj, getLsbD_byteOf _ hi hj]
  simp only [show 8 * i + j < 64 by omega, show 56 - 8 * i + j < 64 by omega, decide_true, Bool.true_and]

theorem wordOf_readW (m : Mem) (a : Addr) : WordOf (m.readW a 64) (wordAt m a) :=
  fun i hi j hj => by rw [readW64_bit m a hi hj, byteOf_wordAt m a hi]

theorem wordOf_iff_rel {w h : BitVec 64} : WordOf w h ↔ WordRel (fun _ => w) (fun _ => h) :=
  ⟨fun hw _ _ i hi j hj => hw i hi j hj, fun hw i hi j hj => hw 0 (by decide) i hi j hj⟩

/-! ## Blocks -/

/-- The first `k` blocks are `F`'s, the others still `m₀`'s. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Block) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

/-- Each block, transformed. -/
def outF (m₀ : Mem) (D : Addr) (g : Nat) (E : Nat → BitVec 64) (j : Nat) : Block :=
  encodeBlock (cryptWords g E (decodeBlock (blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

theorem blocksAt_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Block}
    (h : DInv m₀ m D n n F) : blocksAt m D n = (List.range n).map F := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext; intro t ht
  simp only [blockAt, Vector.getElem_ofFn]
  rw [addr_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + t) / 16 = j by omega,
    show (16 * j + t) % 16 = t by omega]
  simp [Vector.getD, ht]

/-- The schedule's words, as `subkeysAt` reads them. -/
abbrev schedWords (m : Mem) (sched : Addr) (R : Nat) : List (BitVec 64) :=
  (List.range (scheduleLength R)).map fun i => wordAt m (sched + BitVec.ofNat 64 (8 * i))

/-- The block function of each direction. -/
def blockFn (sk : Subkeys) : Direction → Block → Block
  | .encrypt => encryptBlock sk
  | .decrypt => decryptBlock sk

theorem ecb_eq (sk : Subkeys) (d : Direction) (l : List Block) : ecb sk d l = l.map (blockFn sk d) := by
  cases d <;> rfl

theorem schedWords_getD (m : Mem) (sched : Addr) {R i : Nat} (hi : i < scheduleLength R) :
    (schedWords m sched R).getD i 0 = wordAt m (sched + BitVec.ofNat 64 (8 * i)) := by
  simp [schedWords, List.getD_eq_getElem?_getD, hi]

/-- The order of the subkeys in the table for a direction: the stored order, or `decPerm`'s. -/
def dirPerm : Direction → Nat → Nat → Nat
  | .encrypt => fun _ i => i
  | .decrypt => decPerm

theorem dirPerm_lt (d : Direction) {g i : Nat} (hi : i < 8 * g + 2) : dirPerm d g i < 8 * g + 2 := by
  cases d <;> simp only [dirPerm, decPerm] <;> (try split) <;> (try split) <;> omega

theorem outF_spec (d : Direction) (m : Mem) (sched D : Addr) {R : Nat} (hR : R = 18 ∨ R = 24) (j : Nat) :
    outF m D (R / 6) (fun i => (schedWords m sched R).getD (dirPerm d (R / 6) i) 0) j =
      blockFn (subkeysAt m sched R) d (blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases d
  · simp only [outF, blockFn, encryptBlock, subkeysAt, encryptWith_eq hR, dirPerm]
  · simp only [outF, blockFn, decryptBlock, subkeysAt, decryptWith_eq hR, dirPerm]

/-! ## The rounds -/

/-- `p` pairs of rounds of group `i`. -/
def pairsN (E : Nat → BitVec 64) (i p : Nat) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range p).foldl (fun d k => pair (E (2 + 8 * i + 2 * k)) (E (3 + 8 * i + 2 * k)) d) d

theorem pairsN_succ (E : Nat → BitVec 64) (i p : Nat) (d : BitVec 64 × BitVec 64) :
    pairsN E i (p + 1) d = pair (E (2 + 8 * i + 2 * p)) (E (3 + 8 * i + 2 * p)) (pairsN E i p d) := by
  simp [pairsN, List.range_succ, List.foldl_append]

theorem group_eq (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) (i : Nat) :
    group g E d i = if i + 1 < g then
      (fl (pairsN E i 3 d).1 (E (8 + 8 * i)), flinv (pairsN E i 3 d).2 (E (9 + 8 * i)))
      else pairsN E i 3 d := by
  simp only [group, pairsN, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.nil_append, show 2 + 8 * i + 2 * 0 = 2 + 8 * i by omega,
    show 3 + 8 * i + 2 * 0 = 3 + 8 * i by omega, show 2 + 8 * i + 2 * 1 = 4 + 8 * i by omega,
    show 3 + 8 * i + 2 * 1 = 5 + 8 * i by omega, show 2 + 8 * i + 2 * 2 = 6 + 8 * i by omega,
    show 3 + 8 * i + 2 * 2 = 7 + 8 * i by omega]

/-- The first `i` groups. -/
def groupsN (g : Nat) (E : Nat → BitVec 64) (i : Nat) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range i).foldl (group g E) d

theorem groupsN_succ (g : Nat) (E : Nat → BitVec 64) (i : Nat) (d : BitVec 64 × BitVec 64) :
    groupsN g E (i + 1) d = group g E (groupsN g E i d) i := by
  simp [groupsN, List.range_succ, List.foldl_append]

/-! ## The key schedule -/

theorem bytePos_eq : bytePos = pos := rfl

theorem testBit_planeBits (x : BitVec 64) (j n p : Nat) :
    (planeBits x j n).testBit p = (decide (p < n) && x.getLsbD (56 - 8 * bytePos (p / 8) + j)) := by
  induction n with
  | zero => simp [planeBits]
  | succ n ih =>
    rw [planeBits, Nat.testBit_or, ih]
    have hlt : (decide (p < n + 1)) = (decide (p < n) || decide (p = n)) := by
      by_cases h : p < n <;> by_cases h' : p = n <;> simp [h, h'] <;> omega
    rw [hlt]
    by_cases hpn : p = n
    · subst hpn; split <;> simp_all
    · split <;> simp [hpn, Ne.symm hpn]

theorem keyPlane_bit (x : BitVec 64) (j : Nat) {p : Nat} (hp : p < 64) :
    (keyPlane x j).getLsbD p = x.getLsbD (56 - 8 * bytePos (p / 8) + j) := by
  rw [keyPlane, BitVec.getLsbD_ofNat, testBit_planeBits]
  simp [hp]

/-- The planes `sigmaOne` stores hold the constant in every lane. -/
theorem sigma_planes (x : BitVec 64) {b c j : Nat} (hb : b < 8) (hc : c < 8) (hj : j < 8) :
    (keyPlane x j).getLsbD (8 * c + b) = (byteOf x (pos c)).getLsbD j := by
  rw [keyPlane_bit x j (by omega), getLsbD_byteOf x (pos_lt hc) hj, bytePos_eq,
    show (8 * c + b) / 8 = c by omega]

/-- The subkeys of the pairs, `Sigma1 … Sigma6`. -/
def sigE (i : Nat) : BitVec 64 := sigmas.getD i 0

section
variable (KL KR : BitVec 64 × BitVec 64)

/-- The value after each pair: `KA` after the second, `KB` after the third. -/
def kaD1 : BitVec 64 × BitVec 64 := pair (sigE 0) (sigE 1) (KL.1 ^^^ KR.1, KL.2 ^^^ KR.2)
def kaD2 : BitVec 64 × BitVec 64 := pair (sigE 2) (sigE 3) ((kaD1 KL KR).1 ^^^ KL.1, (kaD1 KL KR).2 ^^^ KL.2)
def kaD3 : BitVec 64 × BitVec 64 := pair (sigE 4) (sigE 5) ((kaD2 KL KR).1 ^^^ KR.1, (kaD2 KL KR).2 ^^^ KR.2)

/-- The running value before pair `i`, and `KB` after the last. -/
def kaW : Nat → BitVec 64 × BitVec 64
  | 0 => (KL.1 ^^^ KR.1, KL.2 ^^^ KR.2)
  | 1 => ((kaD1 KL KR).1 ^^^ KL.1, (kaD1 KL KR).2 ^^^ KL.2)
  | 2 => ((kaD2 KL KR).1 ^^^ KR.1, (kaD2 KL KR).2 ^^^ KR.2)
  | _ => kaD3 KL KR
end

/-- The values are the specification's `KA` and `KB` (`kakb`). -/
theorem kaD_eq (kl kr : BitVec 128) :
    kaD2 (hiW kl, loW kl) (hiW kr, loW kr) = (hiW (kakb kl kr).1, loW (kakb kl kr).1) ∧
    kaD3 (hiW kl, loW kl) (hiW kr, loW kr) = (hiW (kakb kl kr).2, loW (kakb kl kr).2) := by
  obtain ⟨h1, h2, h3, h4⟩ := kakb_halves kl kr
  rw [h1, h2, h3, h4]
  exact ⟨rfl, rfl⟩

theorem subkeys_lt4 : (∀ k ∈ Impl.Camellia.subkeys128, k.1 < 4) ∧ (∀ k ∈ Impl.Camellia.subkeys256, k.1 < 4) := by
  decide

theorem subkeys_length : Impl.Camellia.subkeys128.length = 26 ∧ Impl.Camellia.subkeys256.length = 34 := by
  decide

/-- The stored subkeys' bytes are their words', with the values' halves `H v` and `L v`. -/
theorem schedule_of_stores {m : Mem} {S : Addr} {ks : List (Nat × Nat × Bool)} {vs : List (BitVec 128)}
    {H L : Nat → BitVec 64} (hv : ∀ k ∈ ks, k.1 < 4)
    (hg : ∀ v < 4, H v = hiW (vs.getD v 0) ∧ L v = loW (vs.getD v 0))
    (hm : ∀ i < ks.length, ∀ j < 8, m (S + BitVec.ofNat 64 (8 * (0 + i) + j)) =
      byteOf (rotHalf (H (ks.getD i (0, 0, true)).1) (L (ks.getD i (0, 0, true)).1) (ks.getD i (0, 0, true)).2.1
        (ks.getD i (0, 0, true)).2.2) j) :
    bytesAt m S (8 * ks.length) = (subkeyWords vs ks).flatMap wordBytes := by
  have hl : (subkeyWords vs ks).length = ks.length := by simp [subkeyWords]
  rw [← hl]
  refine bytesAt_words m _ S fun i hi j hj => ?_
  rw [hl] at hi
  rw [show 8 * i + j = 8 * (0 + i) + j by omega, hm i hi j hj]
  have hk : ks.getD i (0, 0, true) = ks[i] := by simp [List.getD_eq_getElem?_getD, hi]
  have h4 := hg ks[i].1 (hv _ (List.getElem_mem hi))
  rw [hk, h4.1, h4.2]
  simp only [subkeyWords, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

end VG.Proof.Camellia
