module

-- separate module: the digest parsed to the tree and leaf indices and the lanes' addresses, apart from the calls' proofs

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopCtx
public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopSpec
public import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGenPro
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkDigits
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: the indices and the lanes' addresses

Untrusted: everything here is checked by Lean. `parseIdx` reads the
digest's `tmp_idx_tree` and `tmp_idx_leaf` as big-endian words and leaves
`idx_tree` and `idx_leaf` of `splitDigest` in `sign`'s variables 0 and 1
(`parse_ok`); `treeLanes` with the layer `L` in `r10` and the tree `T` in
`r9` writes `layerTree L T` to every lane's address (`treeG_ok`), as key
generation's `tree_ok` does for the tree 0. (As `verify`'s, whose code is
the same.)
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave treeLanes)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (in_scr disj_scr)
open VG.Proof.SlhDsa.X86_64.KeyGen (lane lane_lt lane_disj seed_adrs_disj bytesAt_split lanesR wp_flatMap)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar os2ip_take os2ip_lt toInt_eq)

/-! ## Bytes and words -/

theorem bytesAt_len (m : Mem) (a : Addr) (k : Nat) : (bytesAt m a k).length = k := Proof.MlKem.bytesAt_length m a k

theorem bswap_read (m : Mem) (a : Addr) : (bswap64 (m.readW a 64)).toNat = Spec.Rsa.os2ip (bytesAt m a 8) := by
  have h := Proof.Bignum.X86_64.WordIO.read_digit (m := m) (src := a) (bs := bytesAt m a 8) (q := 0)
    (by rw [bytesAt_len]) (fun i hi => by simp [bytesAt])
  rw [bytesAt_len] at h
  simp only [Nat.zero_add, Nat.mul_one, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  rw [show a + BitVec.ofNat 64 0 = a by simp] at h
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := os2ip_lt (bytesAt m a 8)
  rw [bytesAt_len] at this
  exact Nat.lt_of_lt_of_le this (by decide)

theorem bytesAt_take' (m : Mem) (a : Addr) {k L : Nat} (h : k ≤ L) : (bytesAt m a L).take k = bytesAt m a k := by
  have e := KeyGen.bytesAt_add m a k (L - k)
  rw [Nat.add_sub_cancel' h] at e
  rw [e, List.take_left' (bytesAt_len _ _ _)]

theorem bytesAt_drop_take (m : Mem) (a : Addr) {d k L : Nat} (h : d + k ≤ L) :
    ((bytesAt m a L).drop d).take k = bytesAt m (a + BitVec.ofNat 64 d) k := by
  have e := KeyGen.bytesAt_add m a d (L - d)
  rw [Nat.add_sub_cancel' (by omega)] at e
  rw [e, List.drop_left' (bytesAt_len _ _ _), bytesAt_take' _ _ (by omega)]

theorem toNat_shl_shr (x : BitVec 64) {k : Nat} (hk : k ≤ 64) : ((x <<< k) >>> k).toNat = x.toNat % 2 ^ (64 - k) := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]

/-! ## The conditional shifts -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `shr rax, k` if `c`. -/
theorem wp_ifShr {c : Prop} [Decidable c] {k : Nat} (hk : c → 1 ≤ k ∧ k ≤ 63)
    (h : ∀ s', Upd s s' .rax (if c then s.gpr .rax >>> k else s.gpr .rax) → WP isa (.block is) s' Q) :
    WP isa (.block ((if c then [Instr.shift .shr .rax k] else []) ++ is)) s Q := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, List.singleton_append]
    exact Levels.wp_shr (hk hc).1 (hk hc).2 fun s' u => h s' (by simpa [hc] using u)
  · simp only [hc, ↓reduceIte, List.nil_append]
    exact h s ⟨by simp [hc], fun _ _ => rfl, rfl, rfl, rfl⟩

/-- `shl rax, k; shr rax, k` if `c`. -/
theorem wp_ifMask {c : Prop} [Decidable c] {k : Nat} (hk : c → 1 ≤ k ∧ k ≤ 63)
    (h : ∀ s', Upd s s' .rax (if c then (s.gpr .rax <<< k) >>> k else s.gpr .rax) → WP isa (.block is) s' Q) :
    WP isa (.block ((if c then [Instr.shift .shl .rax k, .shift .shr .rax k] else []) ++ is)) s Q := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, List.cons_append, List.nil_append]
    refine Levels.wp_shl (hk hc).1 (hk hc).2 fun s₁ u₁ => Levels.wp_shr (hk hc).1 (hk hc).2 fun s₂ u₂ => h s₂ ?_
    refine ⟨by rw [u₂.gpr, u₁.gpr]; simp [hc], fun r hr => by rw [u₂.other _ hr, u₁.other _ hr], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  · simp only [hc, ↓reduceIte, List.nil_append]
    exact h s ⟨by simp [hc], fun _ _ => rfl, rfl, rfl, rfl⟩

/-- `bswap rax`. -/
theorem wp_bswap (h : ∀ s', Upd s s' .rax (bswap64 (s.gpr .rax)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap .rax :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (h _ (Upd.setReg _ _ _))

end

/-! ## The values -/

theorem tree_val {X : List Byte} (hX : X.length = 8) {tl tb : Nat} (h1 : 1 ≤ tl) (h2 : tl ≤ 8) (h4 : tb ≤ 64)
    (x : BitVec 64) (hx : x.toNat = Spec.Rsa.os2ip X) :
    (if tb < 64 then ((if tl < 8 then x >>> (64 - 8 * tl) else x) <<< (64 - tb)) >>> (64 - tb)
      else (if tl < 8 then x >>> (64 - 8 * tl) else x)).toNat = Spec.Rsa.os2ip (X.take tl) % 2 ^ tb := by
  have hy : (if tl < 8 then x >>> (64 - 8 * tl) else x).toNat = Spec.Rsa.os2ip (X.take tl) := by
    split
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx, ← os2ip_take X tl, hX,
        show 64 - 8 * tl = 8 * (8 - tl) by omega, Nat.pow_mul]
    · rw [List.take_of_length_le (by omega), hx]
  split
  · rw [toNat_shl_shr _ (by omega), hy, show 64 - (64 - tb) = tb by omega]
  · rw [hy, show tb = 64 by omega, Nat.mod_eq_of_lt]
    have := os2ip_lt (X.take tl)
    rw [List.length_take, hX] at this
    have hm : min tl 8 ≤ 8 := Nat.min_le_right _ _
    exact Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.pow_le_pow_right (by decide) hm) (by decide))

theorem leaf_val {X : List Byte} (hX : X.length = 8) {ll hp : Nat} (h1 : 1 ≤ ll) (h2 : ll ≤ 2) (h3 : hp ≤ 9)
    (x : BitVec 64) (hx : x.toNat = Spec.Rsa.os2ip X) :
    ((x >>> (64 - 8 * ll)) &&& (BitVec.ofNat 32 (2 ^ hp - 1)).signExtend 64).toNat =
      Spec.Rsa.os2ip (X.take ll) % 2 ^ hp := by
  have hp' : 2 ^ hp - 1 < 2 ^ 31 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) h3; omega
  rw [Levels.sx_ofNat hp', BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx,
    ← os2ip_take X ll, hX, show 64 - 8 * ll = 8 * (8 - ll) by omega, Nat.pow_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ hp - 1 < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod]

/-! ## `vParseIdx` -/

theorem free_vars {L : SL} (hL : L.Ok) : Free L ⟨at' L.S (oKgSave + 48), 32⟩ := by
  have hn := hL.n32
  have eK : oKgSave = 34080 := rfl
  refine .inl ⟨hL.scr_sub (by rw [eK]; omega), fun q hq => ?_⟩
  simp only [SL.prot, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hq
  rcases hq with ((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩)
  · exact Levels.disj_scr L.S (by rw [eK]; omega) (by rw [eK]; omega) (by omega)
  · exact Levels.disj_scr L.S (by rw [eK]; simp only [Layout.oKeys]; omega) (by rw [eK]; omega)
      (by simp only [Layout.oKeys]; omega)
  · exact Levels.disj_scr L.S (by rw [eK]; omega) (by rw [eK]; omega) (by rw [eK]; omega)
  · exact Levels.disj_scr L.S (by rw [eK]; simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
      (by rw [eK]; omega) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact Levels.disj_scr L.S (by rw [eK]; simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
      (by rw [eK]; omega) (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)

/-- `sign`'s variable `i`. -/
abbrev SL.var (L : SL) (i : Nat) : Addr := at' L.S (oKgSave + 48 + 8 * i)

theorem var_sub {L : SL} (_hL : L.Ok) {i : Nat} (hi : i < 4) :
    Region.Sub ⟨L.var i, 8⟩ ⟨at' L.S (oKgSave + 48), 32⟩ := by
  show Region.Sub ⟨at' L.S (oKgSave + 48 + 8 * i), 8⟩ _
  rw [← Levels.at_add]; exact Offset.sub_base _ (by omega)

theorem var_in {L : SL} {g : Reg → BitVec 64} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 4) :
    InRegions t.wr (L.var i) 8 := by
  rw [hc.wr]
  refine ⟨L.SCR, by simp, ?_⟩
  show Region.Contains L.SCR (L.S + BitVec.ofNat 64 (oKgSave + 48 + 8 * i)) 8
  rw [show oKgSave = 34080 from rfl]
  exact Offset.contains_base _ (by omega) (by omega)

theorem ea_var (t : State) (i : Nat) :
    t.ea (Impl.SlhDsa.X86_64.Shake.var i) = t.gpr .rbx + BitVec.ofNat 64 (oKgSave + 48 + 8 * i) := ea_at _ _ _

variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem parse_ok {p : Params} (hp : VPar p) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (Impl.SlhDsa.X86_64.Shake.parseIdx p)) t fun t' => Ctx L g m₀ t' ∧
      t'.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (splitDigest p (bytesAt t.mem (at' L.S Layout.oDigest) p.m)).2.1 ∧
      t'.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (splitDigest p (bytesAt t.mem (at' L.S Layout.oDigest) p.m)).2.2 ∧
      Frame [⟨at' L.S (oKgSave + 48), 32⟩] t.mem t'.mem := by
  have eD : Layout.oDigest = 30304 := rfl
  have rd := hp.rd
  have hm := hp.m
  have hti := hp.ti8
  have hti7 := hp.ti7
  have hli := hp.li
  unfold Impl.SlhDsa.X86_64.Shake.parseIdx
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hin : ∀ {o : Nat}, o + 8 ≤ 65536 → InRegions (t.rd ++ t.wr) (L.S + BitVec.ofNat 64 o) 8 := fun h =>
    Levels.in_scr' (hc.inScr) h
  refine wp_movm (by rw [ea_at, hc.rbx]) (hin (by rw [eD]; omega)) fun t₁ u₁ => wp_bswap fun t₂ u₂ => ?_
  refine wp_ifShr (c := p.treeIdxLen < 8) (k := 64 - 8 * p.treeIdxLen) (fun h => ⟨by omega, by omega⟩) fun t₃ u₃ => ?_
  refine wp_ifMask (c := p.h - p.h / p.d < 64) (k := 64 - (p.h - p.h / p.d)) (fun h => by
    have := hp.tb; have := hp.tb'; have := hp.hd; have := hp.d22; have := hp.hp1; have := hp.hp9; have := hp.hgt; exact ⟨by omega, by omega⟩) fun t₄ u₄ => ?_
  have hb₄ : t₄.gpr .rbx = L.S := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), hc.rbx]
  refine wp_store (a := L.var 0) (by rw [ea_var, hb₄]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact var_in hc (by omega))
    fun t₅ g₅ m₅ r₅ w₅ => ?_
  refine wp_movm (by rw [ea_at, g₅, hb₄])
    (by rw [r₅, w₅, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin (by rw [eD]; omega))
    fun t₆ u₆ => wp_bswap fun t₇ u₇ => ?_
  refine Levels.wp_shr (n := 64 - 8 * p.leafIdxLen) (by omega) (by omega) fun t₈ u₈ => ?_
  refine VG.Proof.SlhDsa.X86_64.wp_andi fun t₉ u₉ => ?_
  have hb₉ : t₉.gpr .rbx = L.S := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
    u₆.other _ (by decide), g₅, hb₄]
  refine wp_store (a := L.var 1) (by rw [ea_var, hb₉])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact var_in hc (by omega))
    fun t₁₀ g₁₀ m₁₀ r₁₀ w₁₀ => WP.block_nil ?_
  have eK : oKgSave = 34080 := rfl
  have hvc : ∀ i < 4, Region.Contains ⟨at' L.S (oKgSave + 48), 32⟩ (L.var i) 8 := fun i hi => by
    show Region.Contains ⟨L.S + BitVec.ofNat 64 (oKgSave + 48), 32⟩ (L.S + BitVec.ofNat 64 (oKgSave + 48 + 8 * i)) 8
    rw [eK]; exact Offset.contains L.S (by omega) (by omega) (by omega)
  have sep01 : Mem.Sep (L.var 0) (64 / 8) (L.var 1) (64 / 8) := Offset.sep L.S (by omega) (by rw [eK]; omega)
    (by rw [eK]; omega)
  -- the digest's words are as on entry
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hm₉ : t₉.mem = t₅.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have rdg : t₅.mem.readW (L.S + BitVec.ofNat 64 (Layout.oDigest + p.mdLen + p.treeIdxLen)) 64 =
      t.mem.readW (L.S + BitVec.ofNat 64 (Layout.oDigest + p.mdLen + p.treeIdxLen)) 64 := by
    rw [m₅, Mem.readW_writeW_sep (Offset.sep L.S (by rw [eK, eD]; omega) (by rw [eD]; omega) (by rw [eK]; omega))
      (by decide), hm₄]
  -- the digest
  have hmd := hp.m
  have Dt : ((bytesAt t.mem (at' L.S Layout.oDigest) p.m).drop p.mdLen).take p.treeIdxLen =
      bytesAt t.mem (L.S + BitVec.ofNat 64 (Layout.oDigest + p.mdLen)) p.treeIdxLen := by
    rw [bytesAt_drop_take _ _ (by omega), Levels.at_add]
  have Dl : ((bytesAt t.mem (at' L.S Layout.oDigest) p.m).drop (p.mdLen + p.treeIdxLen)).take p.leafIdxLen =
      bytesAt t.mem (L.S + BitVec.ofNat 64 (Layout.oDigest + p.mdLen + p.treeIdxLen)) p.leafIdxLen := by
    rw [bytesAt_drop_take _ _ (by omega), Levels.at_add, Nat.add_assoc]
  have htv : (t₄.gpr .rax).toNat = (splitDigest p (bytesAt t.mem (at' L.S Layout.oDigest) p.m)).2.1 := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
    rw [tree_val (bytesAt_len _ _ 8) (by omega) hti (by have := hp.tb; have := hp.tb'; omega) _ (bswap_read _ _),
      bytesAt_take' _ _ hti]
    simp only [splitDigest, toInt_eq, Dt, List.take_of_length_le (Nat.le_of_eq (bytesAt_len _ _ _))]
  have hlv : (t₉.gpr .rax).toNat = (splitDigest p (bytesAt t.mem (at' L.S Layout.oDigest) p.m)).2.2 := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, rdg]
    have hll : 1 ≤ p.leafIdxLen ∧ p.leafIdxLen ≤ 2 := by omega
    rw [leaf_val (bytesAt_len _ _ 8) hll.1 hll.2 hp.hp9 _ (bswap_read _ _), bytesAt_take' _ _ (by omega)]
    simp only [splitDigest, toInt_eq, Dl, List.take_of_length_le (Nat.le_of_eq (bytesAt_len _ _ _)), hp.hd]
  have lt64 : ∀ {x : BitVec 64} {v : Nat}, x.toNat = v → x = BitVec.ofNat 64 v := fun {x v} h => by
    subst h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  -- the registers
  have hg : ∀ r, r ≠ .rax → t₁₀.gpr r = t.gpr r := fun r h => by
    rw [g₁₀, u₉.other _ h, u₈.other _ h, u₇.other _ h, u₆.other _ h, g₅, u₄.other _ h, u₃.other _ h, u₂.other _ h,
      u₁.other _ h]
  have hf : Frame [⟨at' L.S (oKgSave + 48), 32⟩] t.mem t₁₀.mem := by
    rw [m₁₀, hm₉, m₅, hm₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hvc 0 (by omega))).writeW (List.mem_singleton_self _)
      _ (hvc 1 (by omega))
  refine ⟨hc.of_frame hL (by rw [r₁₀, u₉.rd, u₈.rd, u₇.rd, u₆.rd, r₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [w₁₀, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (hg _ (by decide)) (hg _ (by decide))
    (fun r hr _ _ => hg r (by intro e; subst e; revert hr; decide)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact free_vars hL), ?_, ?_, hf⟩
  · rw [m₁₀, Mem.readW_writeW_sep sep01 (by decide), hm₉, m₅, Mem.readW_writeW_self64]
    exact lt64 htv
  · rw [m₁₀, Mem.readW_writeW_self64]
    exact lt64 hlv


/-! ## The lanes' addresses -/

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

end VG.Proof.SlhDsa.X86_64.SignTop
