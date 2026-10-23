module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Absorb
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Chain
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common

/-!
# Streaming TDEA-CMAC on PPC64LE: `absorb`'s chaining path

`chain_wp`: when the data do not fit after the `h` bytes held back,
`chainPath` completes the block held back with the data's first `8 - h`
bytes, chains it (`chainSetup` and a call of the block function) and the
data's `nb` whole blocks after them (`chainLoop_wp`), writes the chaining
value back to the state (`chainDone`), and copies the data's last `rest`
bytes to the bytes held back.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

theorem shr3_ofNat {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem shl3_ofNat {n : Nat} (hn : 8 * n < 2 ^ 64) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hn]
  omega

/-- The whole blocks the path chains after the block held back. -/
abbrev nbOf (len f : Nat) : Nat := (len - f - 1) / 8

/-- The bytes it holds back after them. -/
abbrev restOf (len f : Nat) : Nat := len - f - 8 * nbOf len f

/-- What the path leaves in memory: the chaining value of the block held
back, completed by the data's first `f = 8 - h` bytes, and of the data's
`nb` whole blocks after them; the bytes after those held back. -/
structure ChainMem (m : Mem) (S D : Addr) (len h : Nat) (m' : Mem) : Prop where
  key : ∀ i < 400, m' (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i)
  chain : Spec.Aes.bytesAt m' (S + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m S)) (Spec.Aes.bytesAt m (S + BitVec.ofNat 64 400) 8)
      ([Spec.Aes.bytesAt m (S + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt m D (8 - h)] ++
        Spec.Cmac.blocksAt m (D + BitVec.ofNat 64 (8 - h)) 8 (nbOf len (8 - h)))
  held : Spec.Aes.bytesAt m' (S + BitVec.ofNat 64 408) (restOf len (8 - h)) =
    Spec.Aes.bytesAt m (D + BitVec.ofNat 64 (8 - h + 8 * nbOf len (8 - h))) (restOf len (8 - h))

theorem chain_wp {u : State} {S D W : Addr} {len h : Nat} (he : PathEnv u S D W len h) (hc : 8 - h < len) :
    WP isa chainPath u fun v => PathOut u S W v ∧ ChainMem u.mem S D len h v.mem := by
  have hh := he.hh
  have hl := he.lenLt
  have hS := he.stateFit
  have hD := he.dataFit
  have hWf := he.scrFit
  generalize hf : 8 - h = f at hc ⊢
  have hnb8 : 8 * nbOf len f ≤ len - f - 1 := by show 8 * ((len - f - 1) / 8) ≤ _; omega
  have hnbe : nbOf len f = (len - f - 1) / 8 := rfl
  have hrest : 1 ≤ restOf len f ∧ restOf len f ≤ 8 := by
    show 1 ≤ len - f - 8 * ((len - f - 1) / 8) ∧ len - f - 8 * ((len - f - 1) / 8) ≤ 8; omega
  have hreste : restOf len f = len - f - 8 * nbOf len f := rfl
  generalize hnb : nbOf len f = nb at hnb8 hnbe hreste ⊢
  generalize hr : restOf len f = rest at hrest hreste ⊢
  -- Regions.
  have hWu : (⟨W, 688⟩ : Region) ∈ u.wr := he.scr
  have dataIn : ∀ a n, a + n ≤ len → InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 a) n := fun a n h =>
    ⟨_, List.mem_append_left _ he.data, VG.Offset.contains_base _ h (by omega)⟩
  have stIn : ∀ a n, a + n ≤ 416 → InRegions u.wr (S + BitVec.ofNat 64 a) n := fun a n h =>
    ⟨_, he.state, VG.Offset.contains_base _ h (by omega)⟩
  have dataW : ∀ a n, a + n ≤ len → ∀ r ∈ [(⟨W, 520⟩ : Region)], Region.Disjoint ⟨D + BitVec.ofNat 64 a, n⟩ r :=
    fun a n h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (he.dataScr.sub_right (Region.sub_prefix (by decide))).sub_left (VG.Offset.sub_base _ h)
  have dataS : ∀ a n, a + n ≤ len → Region.Disjoint ⟨D + BitVec.ofNat 64 a, n⟩ ⟨S + BitVec.ofNat 64 400, 16⟩ :=
    fun a n h => (he.dataState.sub_right (VG.Offset.sub_base _ (by decide))).sub_left (VG.Offset.sub_base _ h)
  have keyW : ∀ r ∈ [(⟨W, 520⟩ : Region)], (⟨S, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (he.stateScr.sub_right (Region.sub_prefix (by decide))).sub_left (Region.sub_prefix (by decide))
  have keyS : ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region)], (⟨S, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.base_disjoint _ (by decide) (by omega)
  unfold chainPath
  -- The block held back, completed.
  refine WP.seq_seq (toHeld_copy_wp he (by decide) (by decide) (cnt := f) (by rw [he.r9, hf]) (by omega) (by omega)
    fun v₁ r10₁ g₁ rd₁ wr₁ cp₁ => ?_)
  have m₁S : Frame [⟨S + BitVec.ofNat 64 400, 16⟩] u.mem v₁.mem := fun x hx =>
    cp₁.rest x fun i hi e => hx _ List.mem_cons_self (by
      rw [e, VG.Offset.add_add]
      exact VG.Offset.contains _ (show 400 ≤ 408 + h + i by omega) (show 408 + h + i + 1 ≤ 400 + 16 by omega)
        (by omega))
  have heldB : Spec.Aes.bytesAt v₁.mem (S + BitVec.ofNat 64 408) 8 =
      Spec.Aes.bytesAt u.mem (S + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D f := by
    rw [show 8 = h + f by omega, Proof.Cmac.Stream.bytesAt_append, VG.Offset.add_add]
    congr 1
    · refine Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => ?_
      rw [VG.Offset.add_add]
      exact cp₁.rest _ fun i' hi' => by
        rw [VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    · exact List.map_congr_left fun i hi => cp₁.copied i (List.mem_range.mp hi)
  have v3 : v₁.gpr .r3 = S := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r3]
  have v5 : v₁.gpr .r5 = W := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r5]
  have v6 : v₁.gpr .r6 = BitVec.ofNat 64 len := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r6]
  have v9 : v₁.gpr .r9 = BitVec.ofNat 64 f := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), he.r9, hf]
  have stRd : ∀ (t : State), t.rd = u.rd → t.wr = u.wr → ∀ a n, a + n ≤ 416 →
      InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 a) n := fun t hrd hwr a n h => by
    rw [hrd, hwr]; exact ⟨_, List.mem_append_right _ he.state, VG.Offset.contains_base _ h (by omega)⟩
  have bufW : ∀ (t : State), t.wr = u.wr → InRegions t.wr (W + BitVec.ofNat 64 512) 8 := fun t hwr => by
    rw [hwr]; exact ⟨_, hWu, VG.Offset.contains_base _ (show 512 + 8 ≤ 688 by decide) (by omega)⟩
  -- The counts, and the block held back XORed into the chaining value.
  refine WP.seq ?_
  simp only [chainSetup, mr]
  refine wp_mr fun w₁ x₁ => wp_sub fun w₂ x₂ => wp_subi (by decide) (by decide) fun w₃ x₃ =>
    wp_lsr (by decide) fun w₄ x₄ => wp_sub fun w₅ x₅ => wp_lsl (by decide) fun w₆ x₆ => wp_sub fun w₇ x₇ => ?_
  have g₇ : ∀ r, r ≠ .r12 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → w₇.gpr r = v₁.gpr r := fun r h12 h29 h30 h31 => by
    rw [x₇.other r h31, x₆.other r h12, x₅.other r h31, x₄.other r h30, x₃.other r h30, x₂.other r h30,
      x₁.other r h29]
  have r30₄ : w₄.gpr .r30 = BitVec.ofNat 64 nb := by
    rw [x₄.gpr, x₃.gpr, x₂.gpr, x₁.other _ (by decide), x₁.other _ (by decide), v6, v9,
      VG.Offset.ofNat_sub_ofNat (by omega), VG.Offset.ofNat_sub_ofNat (by omega), shr3_ofNat (by omega), hnbe]
  have r29₇ : w₇.gpr .r29 = D + BitVec.ofNat 64 f := by
    rw [x₇.other _ (by decide), x₆.other _ (by decide), x₅.other _ (by decide), x₄.other _ (by decide),
      x₃.other _ (by decide), x₂.other _ (by decide), x₁.gpr, r10₁]
  have r30₇ : w₇.gpr .r30 = BitVec.ofNat 64 nb := by
    rw [x₇.other _ (by decide), x₆.other _ (by decide), x₅.other _ (by decide), r30₄]
  have a6 : w₄.gpr .r6 = BitVec.ofNat 64 len := by
    rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), x₁.other _ (by decide), v6]
  have a9 : w₄.gpr .r9 = BitVec.ofNat 64 f := by
    rw [x₄.other _ (by decide), x₃.other _ (by decide), x₂.other _ (by decide), x₁.other _ (by decide), v9]
  have r31₇ : w₇.gpr .r31 = BitVec.ofNat 64 rest := by
    rw [x₇.gpr, x₆.other _ (by decide), x₆.gpr, x₅.gpr, x₅.other _ (by decide), r30₄, a6, a9,
      VG.Offset.ofNat_sub_ofNat (by omega), shl3_ofNat (by omega), VG.Offset.ofNat_sub_ofNat (by omega), hreste]
  have rd₇ : w₇.rd = u.rd := by rw [x₇.rd, x₆.rd, x₅.rd, x₄.rd, x₃.rd, x₂.rd, x₁.rd, rd₁]
  have wr₇ : w₇.wr = u.wr := by rw [x₇.wr, x₆.wr, x₅.wr, x₄.wr, x₃.wr, x₂.wr, x₁.wr, wr₁]
  have m₇ : w₇.mem = v₁.mem := by rw [x₇.mem, x₆.mem, x₅.mem, x₄.mem, x₃.mem, x₂.mem, x₁.mem]
  refine wp_ld (a := S + BitVec.ofNat 64 400) (by decide) (by decide)
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide), v3]) (stRd _ rd₇ wr₇ 400 8 (by decide))
    fun w₈ x₈ => ?_
  refine wp_ld (a := S + BitVec.ofNat 64 408) (by decide) (by decide)
    (by rw [x₈.other _ (by decide), g₇ _ (by decide) (by decide) (by decide) (by decide), v3])
    (stRd _ (by rw [x₈.rd, rd₇]) (by rw [x₈.wr, wr₇]) 408 8 (by decide)) fun w₉ x₉ => wp_xor fun w₁₀ x₁₀ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 512) (by decide) (by decide)
    (by rw [x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.other _ (by decide),
      g₇ _ (by decide) (by decide) (by decide) (by decide), v5]; rfl)
    (bufW _ (by rw [x₁₀.wr, x₉.wr, x₈.wr, wr₇])) fun w₁₁ x₁₁ => ?_
  refine wp_addi (by decide) (by decide) fun c x₁₂ => wp_nil ?_
  have gc : ∀ r, r ≠ .r4 → r ≠ .r7 → r ≠ .r9 → r ≠ .r12 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 →
      c.gpr r = v₁.gpr r := fun r h4 h7 h9 h12 h29 h30 h31 => by
    rw [x₁₂.other r h4, x₁₁.gpr, x₁₀.other r h7, x₉.other r h9, x₈.other r h7, g₇ r h12 h29 h30 h31]
  have c5 : c.gpr .r5 = W := by
    rw [gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v5]
  have c4 : c.gpr .r4 = W + BitVec.ofNat 64 512 := by
    rw [x₁₂.gpr, x₁₁.gpr, x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.other _ (by decide),
      g₇ _ (by decide) (by decide) (by decide) (by decide), v5]; rfl
  have c3 : c.gpr .r3 = S := by
    rw [gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3]
  have cR : ∀ r, r = .r29 ∨ r = .r30 ∨ r = .r31 → c.gpr r = w₇.gpr r := by
    rintro r (rfl | rfl | rfl) <;>
      rw [x₁₂.other _ (by decide), x₁₁.gpr, x₁₀.other _ (by decide), x₉.other _ (by decide),
        x₈.other _ (by decide)]
  have rdc : c.rd = u.rd := by rw [x₁₂.rd, x₁₁.rd, x₁₀.rd, x₉.rd, x₈.rd, rd₇]
  have wrc : c.wr = u.wr := by rw [x₁₂.wr, x₁₁.wr, x₁₀.wr, x₉.wr, x₈.wr, wr₇]
  have mc : c.mem = v₁.mem.writeW (W + BitVec.ofNat 64 512)
      (v₁.mem.readW (S + BitVec.ofNat 64 400) 64 ^^^ v₁.mem.readW (S + BitVec.ofNat 64 408) 64) := by
    rw [x₁₂.mem, x₁₁.mem, x₁₀.gpr, x₁₀.mem, x₉.gpr, x₉.other _ (by decide), x₈.gpr, x₉.mem, x₈.mem, m₇]
  have keyIn : ∀ (t : State), t.rd = u.rd → t.wr = u.wr → InRegions (t.rd ++ t.wr) S 384 := fun t hrd hwr => by
    have := stRd t hrd hwr 0 384 (by decide); simpa using this
  have keyScr : Region.Disjoint ⟨S, 384⟩ ⟨W, 640⟩ :=
    (he.stateScr.sub_right (Region.sub_prefix (by decide))).sub_left (Region.sub_prefix (by decide))
  -- The block held back, chained.
  refine WP.seq (encCall_wp c3 c4 c5 (keyIn _ rdc wrc) (L := 688) (by rw [wrc]; exact hWu) (by decide) keyScr
    fun c' rdc' wrc' cc' c'3 c'4 c'5 fc' outc' => ?_)
  have rdc'' : c'.rd = u.rd := by rw [rdc', rdc]
  have wrc'' : c'.wr = u.wr := by rw [wrc', wrc]
  have c'R : ∀ r, r = .r29 ∨ r = .r30 ∨ r = .r31 → c'.gpr r = w₇.gpr r := by
    rintro r (rfl | rfl | rfl) <;> rw [cc' _ (by decide), cR _ (by simp)]
  have env : LoopEnv c' S W (D + BitVec.ofNat 64 f) nb :=
    ⟨keyIn _ rdc'' wrc'', ⟨688, by decide, by rw [wrc'']; exact hWu⟩, keyScr, by omega,
      fun j hj => by
        rw [VG.Offset.add_add, rdc'', wrc'']; exact dataIn _ _ (by omega),
      fun j hj => by
        rw [VG.Offset.add_add]; exact dataW _ _ (by omega) _ (List.mem_singleton_self _),
      by omega⟩
  have h0 : LoopInv c' S W (D + BitVec.ofNat 64 f) nb 0 c' :=
    ⟨c'3, c'4, c'5, by rw [c'R _ (by simp), r29₇, Nat.mul_zero]; exact (BitVec.add_zero _).symm,
      by rw [c'R _ (by simp), r30₇, Nat.sub_zero], fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, (rfl)⟩
  refine WP.seq (chainLoop_wp env h0 fun t ht => ?_)
  -- The chaining value back to the state, and the bytes to hold back.
  refine WP.seq ?_
  simp only [chainDone, mr]
  have tR : ∀ r ∈ preserved, r ≠ .r29 → r ≠ .r30 → t.gpr r = c.gpr r := fun r hr h29 h30 => by
    rw [ht.regs r hr h29 h30, cc' r hr]
  have t31 : t.gpr .r31 = BitVec.ofNat 64 rest := by
    rw [tR _ (by decide) (by decide) (by decide), cR _ (by simp), r31₇]
  refine wp_ld (a := W + BitVec.ofNat 64 512) (by decide) (by decide) (by rw [ht.r5]; rfl)
    (by rw [ht.rd, ht.wr, rdc'', wrc'']
        exact ⟨_, List.mem_append_right _ hWu, VG.Offset.contains_base _ (show 512 + 8 ≤ 688 by decide) (by omega)⟩)
    fun t₁ y₁ => ?_
  refine wp_std (a := S + BitVec.ofNat 64 400) (by decide) (by decide) (by rw [y₁.other _ (by decide), ht.r3])
    (by rw [y₁.wr, ht.wr, wrc'']; exact stIn 400 8 (by decide)) fun t₂ y₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ y₃ => wp_mr fun t₄ y₄ => wp_mr fun t₅ y₅ => wp_nil ?_
  have g₅ : ∀ r, r ≠ .r7 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t₅.gpr r = t.gpr r := fun r h7 h10 h11 h12 => by
    rw [y₅.other r h12, y₄.other r h10, y₃.other r h11, y₂.gpr, y₁.other r h7]
  have rd₅ : t₅.rd = u.rd := by rw [y₅.rd, y₄.rd, y₃.rd, y₂.rd, y₁.rd, ht.rd, rdc'']
  have wr₅ : t₅.wr = u.wr := by rw [y₅.wr, y₄.wr, y₃.wr, y₂.wr, y₁.wr, ht.wr, wrc'']
  have m₅ : t₅.mem = t.mem.writeW (S + BitVec.ofNat 64 400) (t.mem.readW (W + BitVec.ofNat 64 512) 64) := by
    rw [y₅.mem, y₄.mem, y₃.mem, y₂.mem, y₁.gpr, y₁.mem]
  refine copyLoop_wp (src := D + BitVec.ofNat 64 (f + 8 * nb)) (dst := S + BitVec.ofNat 64 408) (n := rest)
    (by omega)
    (by rw [y₅.other _ (by decide), y₄.gpr, y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), ht.r29,
      VG.Offset.add_add])
    (by rw [y₅.other _ (by decide), y₄.other _ (by decide), y₃.gpr, y₂.gpr, y₁.other _ (by decide), ht.r3])
    (by rw [y₅.gpr, y₄.other _ (by decide), y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), t31])
    (fun i hi => by rw [rd₅, wr₅, VG.Offset.add_add]; exact dataIn _ _ (by omega))
    (fun i hi => by rw [wr₅, VG.Offset.add_add]; exact stIn _ _ (by omega))
    (fun i hi i' hi' => by
      rw [VG.Offset.add_add, VG.Offset.add_add]; exact state_ne_data he.dataState hD (by omega) (by omega))
    fun v hv => ?_
  -- The memory.
  have FR : ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region)],
      r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩] := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have FW : ∀ r ∈ [(⟨W, 520⟩ : Region)], r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩] := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  have s400 : (⟨S + BitVec.ofNat 64 400, 16⟩ : Region).Contains (S + BitVec.ofNat 64 400) (64 / 8) :=
    VG.Offset.contains_base _ (show 0 + 64 / 8 ≤ 16 by decide) (by decide) |> fun h => by simpa using h
  have Fc : Frame [⟨W, 520⟩] v₁.mem c.mem := by
    rw [mc]
    exact (Frame.refl _ _).writeW List.mem_cons_self _
      (VG.Offset.contains_base _ (show 512 + 64 / 8 ≤ 520 by decide) (by omega))
  have Fc' : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem c'.mem :=
    ((m₁S.mono FR).trans (Fc.mono FW)).trans (fc'.mono FW)
  have Ft : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem t.mem := Fc'.trans (ht.frame.mono FW)
  have F₅ : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem t₅.mem := by
    rw [m₅]; exact Ft.writeW List.mem_cons_self _ s400
  have Fv : Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem v.mem := F₅.trans fun x hx =>
    hv.rest x fun i hi e => hx _ List.mem_cons_self (by
      rw [e, VG.Offset.add_add]
      exact VG.Offset.contains _ (show 400 ≤ 408 + i by omega) (show 408 + i + 1 ≤ 400 + 16 by omega) (by omega))
  have dataD : ∀ a n, a + n ≤ len → ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩],
      Region.Disjoint ⟨D + BitVec.ofNat 64 a, n⟩ r := fun a n h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dataS a n h
    · exact dataW a n h _ (List.mem_singleton_self _)
  have keyD : ∀ r ∈ [(⟨S + BitVec.ofNat 64 400, 16⟩ : Region), ⟨W, 520⟩], (⟨S, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact keyS _ (List.mem_singleton_self _)
      · exact keyW _ (List.mem_singleton_self _)
  have dataEq : ∀ {m : Mem}, Frame [⟨S + BitVec.ofNat 64 400, 16⟩, ⟨W, 520⟩] u.mem m → ∀ a n, a + n ≤ len →
      Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) n = Spec.Aes.bytesAt u.mem (D + BitVec.ofNat 64 a) n :=
    fun hF a n h => List.map_congr_left fun i hi => hF.bytes (R := ⟨D + BitVec.ofNat 64 a, n⟩) (dataD a n h)
      (by show n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  refine ⟨⟨fun r hr h29 h30 h31 => ?_, ?_, by rw [hv.rd, rd₅], by rw [hv.wr, wr₅], ?_⟩, ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · obtain ⟨h0, -, h4, -, -, h7, -, h9, h10, h11, h12⟩ := preserved_ne r hr
    rw [hv.regs r h0 h10 h11 h12, g₅ r h7 h10 h11 h12, tR r hr h29 h30, gc r h4 h7 h9 h12 h29 h30 h31,
      g₁ r h0 h10 h11 h12]
  · rw [hv.regs _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide)
      (by decide), ht.r5]
  · exact Fv.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, VG.Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · exact Fv.bytes (R := ⟨S, 400⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.base_disjoint _ (by decide) (by omega)
      · exact (he.stateScr.sub_right (Region.sub_prefix (by decide))).sub_left (Region.sub_prefix (by decide)))
      (by show 400 ≤ 2 ^ 64; decide) hi
  · -- The chaining value.
    rw [hf, hnb]
    have e400 : Spec.Aes.bytesAt v.mem (S + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt t₅.mem (S + BitVec.ofNat 64 400) 8 :=
      Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => hv.rest _ fun i' hi' => by
        rw [VG.Offset.add_add, VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    have kc : Spec.TripleDes.scheduleAt c.mem S = Spec.TripleDes.scheduleAt u.mem S :=
      Proof.TripleDes.scheduleAt_eq_of_frame _ ((m₁S.mono FR).trans (Fc.mono FW)) keyD
    have kc' : Spec.TripleDes.scheduleAt c'.mem S = Spec.TripleDes.scheduleAt u.mem S :=
      Proof.TripleDes.scheduleAt_eq_of_frame _ Fc' keyD
    have bl : Spec.Cmac.blocksAt c'.mem (D + BitVec.ofNat 64 f) 8 nb =
        Spec.Cmac.blocksAt u.mem (D + BitVec.ofNat 64 f) 8 nb :=
      List.map_congr_left fun j hj => by
        have hj := List.mem_range.mp hj
        rw [VG.Offset.add_add]; exact dataEq Fc' _ _ (by omega)
    have c400 : Spec.Aes.bytesAt v₁.mem (S + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt u.mem (S + BitVec.ofNat 64 400) 8 :=
      Proof.CmacTripleDes.Stream.bytesAt_congr fun i hi => cp₁.rest _ fun i' hi' => by
        rw [VG.Offset.add_add, VG.Offset.add_add]; exact VG.Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
    rw [e400, m₅, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW, ht.buf, enc_bytes outc', kc',
      kc, bl, mc, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_xor, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, c400, heldB, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · -- The bytes held back.
    rw [hf, hnb, hr]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [hv.copied i hi]
    exact F₅.bytes (R := ⟨D + BitVec.ofNat 64 (f + 8 * nb), rest⟩) (dataD _ _ (by omega)) (by show rest ≤ 2 ^ 64; omega) hi

end VG.Proof.CmacTripleDes.Stream.PPC64LE
