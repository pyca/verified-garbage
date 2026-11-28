module

-- separate module: the chains, a stage of `xmssPk`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkWots
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkDigits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# SLH-DSA on x86-64, `xmssPk`: the WOTS⁺ chains

The blocks of `chainGroup` (`Impl/SlhDsa/X86_64/Verify.lean`): each lane's
chain `min(c₀ + k, len - 1)` and its digit (`chainOf_ok`), the chain's
signature value (`chainSig_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (setField setFieldR)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_subi wp_movzx8)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add wp_sub wp_and in_scr in_scr')

/-- `x - ((x - L) & -((L - x) >> 63))`: the lesser of `x` and `L`. -/
theorem clamp_eq {x L : Nat} (hx : x < 2 ^ 62) (hL : L < 2 ^ 62) :
    BitVec.ofNat 64 x - ((BitVec.ofNat 64 x - BitVec.ofNat 64 L) &&&
      ((0 : BitVec 64) - (BitVec.ofNat 64 L - BitVec.ofNat 64 x) >>> 63)) = BitVec.ofNat 64 (min x L) := by
  by_cases h : x ≤ L
  · have hs : (BitVec.ofNat 64 L - BitVec.ofNat 64 x) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [hs, Nat.min_eq_left h]
    simp
  · have hs : (BitVec.ofNat 64 L - BitVec.ofNat 64 x) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [hs, Nat.min_eq_right (by omega), show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    bv_omega

theorem setw_ofNat32 {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x).setWidth 64 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]

theorem oVar10 : Layout.oVar 1 0 = 2576 := rfl
theorem oVar11 : Layout.oVar 1 1 = 2584 := rfl
theorem oVar12 : Layout.oVar 1 2 = 2592 := rfl
theorem oDigits_eq : Layout.oDigits = 30368 := rfl

/-- Lane `k`'s chain, `c = min(c₀ + k, len - 1)` for `c₀` in variable 0, in
`r10`, and its digit, the byte at `oDigits + c`, in `r11`. -/
theorem chainOf_ok {p : Params} (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128) {k' c₀ : Nat} (hk : c₀ + k' < 2 ^ 31)
    {s : State} {S : Addr} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .r10 = BitVec.ofNat 64 (min (c₀ + k') (p.len - 1)) →
      s'.gpr .r11 = BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)))).toNat →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainOf p k' ++ is)) s Q := by
  simp only [Impl.SlhDsa.X86_64.Verify.chainOf, List.cons_append, List.nil_append]
  refine wp_movm (a := at' S (Layout.oVar 1 0))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hbx])
    (by rw [oVar10]; exact in_scr' hw (by omega)) fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ => wp_sub fun s₄ u₄ => ?_
  refine wp_shri (by decide) (by decide) fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ => ?_
  refine wp_mov32i fun s₈ u₈ => wp_sub fun s₉ u₉ => wp_and fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => ?_
  have hc : min (c₀ + k') (p.len - 1) < 128 := by omega
  have hx : s₂.gpr .r10 = BitVec.ofNat 64 (c₀ + k') := by
    rw [u₂.gpr, u₁.gpr, hv0, sx_ofNat (by omega)]; exact (BitVec.ofNat_add _ _).symm
  have hx₅ : s₅.gpr .r10 = BitVec.ofNat 64 (c₀ + k') := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hx]
  have ha₅ : s₅.gpr .rax = (BitVec.ofNat 64 (p.len - 1) - BitVec.ofNat 64 (c₀ + k')) >>> 63 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), hx, setw_ofNat32 (by omega)]
  have hc₉ : s₉.gpr .rcx = BitVec.ofNat 64 (c₀ + k') - BitVec.ofNat 64 (p.len - 1) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, hx₅, sx_ofNat (by omega)]
  have hd₉ : s₉.gpr .rdx = 0 - (BitVec.ofNat 64 (p.len - 1) - BitVec.ofNat 64 (c₀ + k')) >>> 63 := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ha₅]; rfl
  have h10 : s₁₁.gpr .r10 = BitVec.ofNat 64 (min (c₀ + k') (p.len - 1)) := by
    rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), hx₅, hc₉, hd₉]
    exact clamp_eq (by omega) (by omega)
  have hb₁₁ : s₁₁.gpr .rbx = S := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx]
  have hm : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₁₁.rd = s.rd := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hea : s₁₁.ea { base := .rbx, index := some .r10, scale := 1, disp := (Layout.oDigits : Int) } =
      at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)) := by
    simp only [State.ea, hb₁₁, h10, BitVec.mul_one, BitVec.ofInt_natCast]
    rw [at', BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
  refine wp_movzx8 hea (by rw [hrd, hwr]; exact in_scr' hw (by rw [oDigits_eq]; omega)) fun s₁₂ u₁₂ => ?_
  refine k s₁₂ (fun g h1 h2 h3 h4 h5 => ?_) (by rw [u₁₂.mem, hm]) (by rw [u₁₂.rd, hrd]) (by rw [u₁₂.wr, hwr])
    (by rw [u₁₂.other _ (by decide), h10]) (by rw [u₁₂.gpr, hm]; apply BitVec.eq_of_toNat_eq; simp)
  rw [u₁₂.other _ h5, u₁₁.other _ h4, u₁₀.other _ h2, u₉.other _ h3, u₈.other _ h3, u₇.other _ h2,
    u₆.other _ h2, u₅.other _ h1, u₄.other _ h1, u₃.other _ h1, u₂.other _ h4, u₁.other _ h4]

/-- `rsi ← sig + c·n` and chain `c`'s signature value, the `n` bytes there,
copied to lane `k`'s message. -/
theorem sigLane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {k' c : Nat} (hk' : k' < 4)
    (hc : c < p.len) {s : State} {S sig : Addr} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h10 : s.gpr .r10 = BitVec.ofNat 64 c) (h13 : s.gpr .r13 = sig)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + sL ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rsi → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA k' + p.n + 32)) p.n = bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n →
      Frame [⟨at' S (Layout.laneA k' + p.n + 32), p.n⟩] s.mem s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainSig p ++
      (Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
      is))) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  have hla : Layout.laneA k' + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
  rw [hmsg]
  simp only [Impl.SlhDsa.X86_64.Verify.chainSig, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => Levels.mulN_ok hn (r := .rsi) (tmp := .rax) (by decide) fun s₂ h₂ g₂ m₂ r₂ w₂ => ?_
  refine Levels.wp_add fun s₃ u₃ => WP.block_append ?_
  have hsi : s₃.gpr .rsi = sig + BitVec.ofNat 64 (c * p.n) := by
    rw [u₃.gpr, h₂, u₁.gpr, h10, g₂ _ (by decide) (by decide), u₁.other _ (by decide), h13, BitVec.add_comm,
      ← BitVec.ofNat_mul]
  have hb₃ : s₃.gpr .rbx = S := by
    rw [u₃.other _ (by decide), g₂ _ (by decide) (by decide), u₁.other _ (by decide), hbx]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, m₂, u₁.mem]
  have hr₃ : s₃.rd = s.rd := by rw [u₃.rd, r₂, u₁.rd]
  have hw₃ : s₃.wr = s.wr := by rw [u₃.wr, w₂, u₁.wr]
  have hsub : ∀ {o l : Nat}, o + l ≤ c * p.n + p.n → Region.Sub ⟨sig + BitVec.ofNat 64 o, l⟩ ⟨sig, sL⟩ :=
    fun h => Offset.sub_base sig (by omega)
  refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
    (fun j hj => by rw [hw₃, hb₃]; exact in_scr hw (by omega))
    (fun j hj => ⟨_, List.mem_append_left _ (by rw [hr₃]; exact hsr), by
      rw [hsi, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base sig (by omega) (by omega)⟩)
    (by
      rw [hb₃, hsi, BitVec.add_assoc, ← BitVec.ofNat_add, e8, Nat.add_zero]
      exact ((hss.sub_left (hsub (by omega))).sub_right (Offset.sub_base S (by omega))).symm)
    (by omega) (by omega)) fun s₄ c₄ => ?_
  rw [hb₃, hsi, e8, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_zero] at c₄
  have eA : at' S (Layout.laneA k' + p.n + 32) = S + BitVec.ofNat 64 (Layout.laneA k' + (p.n + 32)) := by
    rw [at', Nat.add_assoc]
  refine k s₄ (fun g h₁ h₂ => by rw [c₄.gpr _ h₁, u₃.other _ h₂, g₂ _ h₂ h₁, u₁.other _ h₂])
    (by rw [c₄.rd, hr₃]) (by rw [c₄.wr, hw₃]) ?_ (by rw [← hm₃, eA]; exact c₄.frame)
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [eA, ← hm₃]
  exact c₄.bytes i (List.mem_range.mp hi)

/-- `((d ^ v) & -((v - d) >> 63)) ^ d`: the lesser of `v` and `d`. -/
theorem minsel_eq {v d : Nat} (hv : v < 2 ^ 62) (hd : d < 2 ^ 62) :
    ((BitVec.ofNat 64 d ^^^ BitVec.ofNat 64 v) &&& ((0 : BitVec 64) - (BitVec.ofNat 64 v - BitVec.ofNat 64 d) >>> 63)) ^^^
      BitVec.ofNat 64 d = BitVec.ofNat 64 (min v d) := by
  by_cases h : d ≤ v
  · have hs : (BitVec.ofNat 64 v - BitVec.ofNat 64 d) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [hs, Nat.min_eq_right h]
    simp
  · have hs : (BitVec.ofNat 64 v - BitVec.ofNat 64 d) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [hs, Nat.min_eq_left (by omega), show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm (BitVec.ofNat 64 d), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Lane `k`'s chain set up, and the least digit so far (variable 2). -/
structure LaneInit (p : Params) (S : Addr) (k' idx c : Nat) (X : List Byte) (m : Mem) : Prop where
  fields : bytesAt m (at' S (Layout.laneA k' + p.n + 16)) 12 = toByte 0 4 ++ toByte idx 4 ++ toByte c 4
  value : bytesAt m (at' S (Layout.laneA k' + p.n + 32)) p.n = X

theorem bytes12_split (m : Mem) (S : Addr) (a : Nat) :
    bytesAt m (at' S a) 12 = bytesAt m (at' S a) 4 ++ bytesAt m (at' S (a + 4)) 4 ++ bytesAt m (at' S (a + 8)) 4 := by
  rw [show (12 : Nat) = 4 + (4 + 4) from rfl, at', at', at', bytesAt_split2, bytesAt_split2, Nat.add_assoc,
    List.append_assoc]

/-- Lane `k`'s set-up in `chainLanes`: its address's type (`WOTS_HASH`), key
pair and chain `c = min(c₀ + k, len - 1)`, its value chain `c`'s signature
value, and variable 2 the lesser of it and chain `c`'s digit. -/
theorem laneInit_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {k' c₀ v idx : Nat} (hk' : k' < 4) (hc₀ : c₀ + 4 < 2 ^ 31) (hv : v < 2 ^ 62) (hidx : idx < 2 ^ 32)
    {s : State} {S sig : Addr} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hv2 : s.mem.readW (at' S (Layout.oVar 1 2)) 64 = BitVec.ofNat 64 v)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + sL ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.rd = s.rd → s'.wr = s.wr →
      LaneInit p S k' idx (min (c₀ + k') (p.len - 1))
        (bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k') (p.len - 1) * p.n)) p.n) s'.mem →
      s'.mem.readW (at' S (Layout.oVar 1 2)) 64 =
        BitVec.ofNat 64 (min v (s.mem (at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)))).toNat) →
      Frame [⟨at' S (Layout.laneA k' + p.n + 16), 16 + p.n⟩, ⟨at' S (Layout.oVar 1 2), 8⟩] s.mem s'.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.chainOf p k' ++
      setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 0 ++
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
      Impl.SlhDsa.X86_64.Verify.chainSig p ++
      Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
      ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63,
        .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .r11),
        .alu .xor .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .and .rax (.reg .rdx),
        .alu .xor .rax (.reg .r11), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] : List Instr)) ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  rw [hadr]
  have hla : Layout.laneA k' + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hla' : 3296 ≤ Layout.laneA k' := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  obtain ⟨c, hc⟩ : ∃ c, c = min (c₀ + k') (p.len - 1) := ⟨_, rfl⟩
  rw [← hc] at k
  have hcl : c < p.len := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = Layout.laneA k' + p.n := ⟨_, rfl⟩
  have hv8 : (⟨at' S (Layout.oVar 1 2), 8⟩ : Region).Contains (at' S (Layout.oVar 1 2)) (64 / 8) :=
    Region.contains_self _ _
  have hvd : ∀ {o l : Nat}, A + 16 ≤ o → o + l ≤ A + 32 + p.n →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, l⟩ : Region)], Region.Disjoint ⟨at' S (Layout.oVar 1 2), 8⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [oVar12]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hdj : ∀ a c : Nat, a + 4 ≤ c ∨ c + 4 ≤ a → a + 4 ≤ 2 ^ 16 → c + 4 ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], Region.Disjoint ⟨S + BitVec.ofNat 64 a, 4⟩ r :=
    fun a c h h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S h (by omega) (by omega)
  have hsub : ∀ {o l : Nat}, A + 16 ≤ o → o + l ≤ A + 32 + p.n →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, l⟩ : Region)], ∃ r' ∈ [(⟨at' S (Layout.laneA k' + p.n + 16), 16 + p.n⟩ : Region),
        ⟨at' S (Layout.oVar 1 2), 8⟩], Region.Sub r r' :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub S (by omega) (by omega)⟩
  simp only [List.append_assoc]
  -- the chain and its digit
  refine chainOf_ok hlen1 hlen (by omega) hbx hv0 hw fun s₁ g₁ m₁ r₁ w₁ h10₁ h11₁ => ?_
  rw [← hc] at h10₁ h11₁
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hin : ∀ (t : State) (o : Nat), t.gpr .rbx = S → t.wr = s.wr → o + 4 ≤ 2 ^ 16 →
      InRegions t.wr (t.gpr .rbx + BitVec.ofNat 64 o) 4 := fun t o h₁ h₂ ho => by
    rw [h₁, h₂]; exact in_scr hw ho
  -- the fields
  refine setField_ok (by decide) (by decide) (hin s₁ _ hb₁ w₁ (by omega)) fun s₂ f₂ => ?_
  rw [hb₁] at f₂
  have hb₂ : s₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  have hidx' : (BitVec.ofNat 64 idx).toNat = idx := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 idx := by
    rw [f₂.gpr _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h12]
  refine setFieldR_ok (by decide) (by rw [h12₂, hidx']; exact hidx) (hin s₂ _ hb₂ (by rw [f₂.wr, w₁]) (by omega))
    fun s₃ f₃ => ?_
  rw [hb₂, h12₂, hidx'] at f₃
  have hb₃ : s₃.gpr .rbx = S := by rw [f₃.gpr _ (by decide), hb₂]
  have h10₃ : s₃.gpr .r10 = BitVec.ofNat 64 c := by rw [f₃.gpr _ (by decide), f₂.gpr _ (by decide), h10₁]
  have hc' : (BitVec.ofNat 64 c).toNat = c := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine setFieldR_ok (by decide) (by rw [h10₃, hc']; omega) (hin s₃ _ hb₃ (by rw [f₃.wr, f₂.wr, w₁]) (by omega))
    fun s₄ f₄ => ?_
  rw [hb₃, h10₃, hc'] at f₄
  have hb₄ : s₄.gpr .rbx = S := by rw [f₄.gpr _ (by decide), hb₃]
  have hg₄ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → g ≠ .r11 → s₄.gpr g = s.gpr g := fun g h1 h2 h3 h4 h5 => by
    rw [f₄.gpr _ h1, f₃.gpr _ h1, f₂.gpr _ h1, g₁ _ h1 h2 h3 h4 h5]
  have hw₄ : s₄.wr = s.wr := by rw [f₄.wr, f₃.wr, f₂.wr, w₁]
  have hr₄ : s₄.rd = s.rd := by rw [f₄.rd, f₃.rd, f₂.rd, r₁]
  -- the signature value
  refine sigLane_ok hn hk' hcl hb₄ (by rw [f₄.gpr _ (by decide), h10₃])
    (by rw [hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h13]) (by rw [hw₄]; exact hw)
    (by rw [hr₄]; exact hsr) hsfit hss hsL fun s₅ g₅ r₅ w₅ v₅ f₅ => ?_
  have hb₅ : s₅.gpr .rbx = S := by rw [g₅ _ (by decide) (by decide), hb₄]
  -- variable 2, which the stores so far leave
  have hv2₅ : s₅.mem.readW (at' S (Layout.oVar 1 2)) 64 = BitVec.ofNat 64 v := by
    rw [f₅.readW hv8 (by rw [at']; exact hvd (by omega) (by omega)) (by decide),
      f₄.frame.readW hv8 (hvd (by omega) (by omega)) (by decide),
      f₃.frame.readW hv8 (hvd (by omega) (by omega)) (by decide),
      f₂.frame.readW hv8 (hvd (by omega) (by omega)) (by decide), m₁, hv2]
  have hd₅ : s₅.gpr .r11 = BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + c))).toNat := by
    rw [g₅ _ (by decide) (by decide), f₄.gpr _ (by decide), f₃.gpr _ (by decide), f₂.gpr _ (by decide), h11₁]
  have hwr₅ : s₅.wr = s.wr := by rw [w₅, hw₄]
  have hrd₅ : s₅.rd = s.rd := by rw [r₅, hr₄]
  have hxv : ∀ t : State, t.gpr .rbx = S → t.ea (Impl.SlhDsa.X86_64.Verify.xv 2) = at' S (Layout.oVar 1 2) :=
    fun t h => by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, h]
  -- the least digit
  refine wp_movm (hxv s₅ hb₅) (by rw [hrd₅, hwr₅, oVar12]; exact in_scr' hw (by omega)) fun s₆ u₆ => ?_
  refine wp_sub fun s₇ u₇ => wp_shri (by decide) (by decide) fun s₈ u₈ => wp_mov32i fun s₉ u₉ => ?_
  refine wp_sub fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => ?_
  have hb₁₁ : s₁₁.gpr .rbx = S := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), hb₅]
  have hm₁₁ : s₁₁.mem = s₅.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have hrw₁₁ : s₁₁.rd ++ s₁₁.wr = s.rd ++ s.wr := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, hrd₅, hwr₅]
  refine Proof.Sha3.X86_64.wp_xorm (hxv s₁₁ hb₁₁) (by rw [hrw₁₁, oVar12]; exact in_scr' hw (by omega))
    fun s₁₂ u₁₂ => ?_
  refine wp_and fun s₁₃ u₁₃ => Proof.Sha3.X86_64.wp_xor fun s₁₄ u₁₄ => ?_
  have hb₁₄ : s₁₄.gpr .rbx = S := by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), hb₁₁]
  refine Proof.Sha3.X86_64.wp_store (hxv s₁₄ hb₁₄)
    (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, hwr₅, oVar12]; exact in_scr hw (by omega))
    fun s₁₅ g₁₅ m₁₅ r₁₅ w₁₅ => ?_
  -- the value stored
  have hd11 : ∀ t : State, (∀ g, g ≠ .rax → g ≠ .rdx → t.gpr g = s₅.gpr g) → t.gpr .r11 = BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + c))).toNat :=
    fun t h => by rw [h _ (by decide) (by decide), hd₅]
  have hrax : s₁₄.gpr .rax = BitVec.ofNat 64 (min v (s.mem (at' S (Layout.oDigits + c))).toNat) := by
    have hdx : s₁₀.gpr .rdx = 0 - (BitVec.ofNat 64 v - BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + c))).toNat) >>> 63 := by
      rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, hv2₅, u₆.other _ (by decide), hd₅]; rfl
    have h11₁₀ : s₁₀.gpr .r11 = BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + c))).toNat := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), hd₅]
    have h11₁₃ : s₁₃.gpr .r11 = BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + c))).toNat := by
      rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), h11₁₀]
    have hdx₁₂ : s₁₂.gpr .rdx = s₁₀.gpr .rdx := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]
    have hax₁₂ : s₁₂.gpr .rax = BitVec.ofNat 64 (s.mem (at' S (Layout.oDigits + c))).toNat ^^^ BitVec.ofNat 64 v := by
      rw [u₁₂.gpr, u₁₁.gpr, h11₁₀, hm₁₁, hv2₅]
    rw [u₁₄.gpr, u₁₃.gpr, h11₁₃, hax₁₂, hdx₁₂, hdx]
    exact minsel_eq hv (by have := (s.mem (at' S (Layout.oDigits + c))).isLt; omega)
  have hm₁₅ : s₁₅.mem = s₅.mem.writeW (at' S (Layout.oVar 1 2)) (BitVec.ofNat 64 (min v (s.mem (at' S (Layout.oDigits + c))).toNat)) := by
    rw [m₁₅, hrax, u₁₄.mem, u₁₃.mem, u₁₂.mem, hm₁₁]
  have F₁₅ : Frame [⟨at' S (Layout.oVar 1 2), 8⟩] s₅.mem s₁₅.mem := by
    rw [hm₁₅]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have hvs : ∀ r ∈ [(⟨at' S (Layout.oVar 1 2), 8⟩ : Region)], ∀ {o l : Nat}, A + 16 ≤ o → o + l ≤ A + 32 + p.n →
      Region.Disjoint ⟨S + BitVec.ofNat 64 o, l⟩ r := fun r hr o l h₁ h₂ => by
    simp only [List.mem_singleton] at hr; subst hr; rw [oVar12]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  refine k s₁₅ (fun g h1 h2 h3 h4 h5 h6 => ?_) ?_ ?_ ⟨?_, ?_⟩ ?_ ?_
  · rw [g₁₅, u₁₄.other _ h1, u₁₃.other _ h1, u₁₂.other _ h1, u₁₁.other _ h1, u₁₀.other _ h3, u₉.other _ h3,
      u₈.other _ h1, u₇.other _ h1, u₆.other _ h1, g₅ _ h1 h4, hg₄ _ h1 h2 h3 h5 h6]
  · rw [r₁₅, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, hrd₅]
  · rw [w₁₅, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, hwr₅]
  · rw [bytes12_split]
    have e₃ : bytesAt s₁₅.mem (at' S (Layout.laneA k' + p.n + 16 + 8)) 4 = toByte c 4 := by
      rw [bytesAt_frame F₁₅ (fun r hr => hvs r hr (by omega) (by omega)) (by decide),
        bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
          (by decide), show Layout.laneA k' + p.n + 16 + 8 = Layout.laneA k' + p.n + 24 by omega]
      exact f₄.bytes
    have e₂ : bytesAt s₁₅.mem (at' S (Layout.laneA k' + p.n + 16 + 4)) 4 = toByte idx 4 := by
      rw [bytesAt_frame F₁₅ (fun r hr => hvs r hr (by omega) (by omega)) (by decide),
        bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
          (by decide), show Layout.laneA k' + p.n + 16 + 4 = Layout.laneA k' + p.n + 20 by omega,
        bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide)]
      exact f₃.bytes
    have e₁ : bytesAt s₁₅.mem (at' S (Layout.laneA k' + p.n + 16)) 4 = toByte 0 4 := by
      rw [bytesAt_frame F₁₅ (fun r hr => hvs r hr (by omega) (by omega)) (by decide),
        bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
          (by decide),
        bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₃.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide)]
      exact f₂.bytes
    rw [e₁, e₂, e₃]
  · have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hcl
    have hsd : ∀ o, o + 4 ≤ 2 ^ 16 → ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, 4⟩ : Region)],
        Region.Disjoint ⟨sig + BitVec.ofNat 64 (c * p.n), p.n⟩ r := fun o ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hss.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S ho)
    rw [bytesAt_frame F₁₅ (fun r hr => by rw [at']; exact hvs r hr (by omega) (by omega)) (by omega), v₅,
      bytesAt_frame f₄.frame (hsd _ (by omega)) (by omega), bytesAt_frame f₃.frame (hsd _ (by omega)) (by omega),
      bytesAt_frame f₂.frame (hsd _ (by omega)) (by omega), m₁]
  · rw [hm₁₅, Mem.readW_writeW_self64]
  · rw [← m₁]
    refine (f₂.frame.sub (hsub (by omega) (by omega))).trans ((f₃.frame.sub (hsub (by omega) (by omega))).trans
      ((f₄.frame.sub (hsub (by omega) (by omega))).trans ((f₅.sub ?_).trans (F₁₅.sub ?_))))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub S (by omega) (by omega)⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `cmp r64, m64`, setting ZF and CF. -/
theorem wp_cmpm {d : Reg} {m : MemOp} {a : Addr} {s : State} {is : List Instr} {Q : State → Prop}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d - s.mem.readW a 64 == 0) →
      s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW a 64).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem m) :: is)) s Q := by
  refine Proof.Sha3.X86_64.WP.cons (s' := arithFlags s (s.gpr d - s.mem.readW a 64) ((s.gpr d).toNat < (s.mem.readW a 64).toNat)
    (subOverflow (s.gpr d) (s.mem.readW a 64) (s.gpr d - s.mem.readW a 64))) ?_ (k _ rfl rfl rfl rfl rfl rfl)
  simp [reduceExec, execAlu, readSrc, State.load64, ha, hin]

/-- After step `j` (variable 1), lane `k`: its signature value back if its
digit is above `j`. -/
theorem restore_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {k' c₀ j : Nat} (hk' : k' < 4) (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 2 ^ 32)
    {s : State} {S sig : Addr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h13 : s.gpr .r13 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hv1 : s.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + sL ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA k' + p.n + 32)) p.n =
        (if j < (s.mem (at' S (Layout.oDigits + min (c₀ + k') (p.len - 1)))).toNat then
          bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k') (p.len - 1) * p.n)) p.n
        else bytesAt s.mem (at' S (Layout.laneA k' + p.n + 32)) p.n) →
      Frame [⟨at' S (Layout.laneA k' + p.n + 32), p.n⟩] s.mem s'.mem → Q s') :
    WP isa (Impl.SlhDsa.X86_64.Verify.restoreLane p k') s Q := by
  unfold Impl.SlhDsa.X86_64.Verify.restoreLane
  refine WP.seq (chainOf_ok hlen1 hlen (by omega) hbx hv0 hw fun s₁ g₁ m₁ r₁ w₁ h10₁ h11₁ => ?_)
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  refine wp_cmpm (a := at' S (Layout.oVar 1 1))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hb₁])
    (by rw [r₁, w₁, oVar11]; exact in_scr' hw (by omega)) fun s₂ g₂ m₂ r₂ w₂ z₂ c₂ => WP.block_nil ?_
  obtain ⟨c, hc⟩ : ∃ c, c = min (c₀ + k') (p.len - 1) := ⟨_, rfl⟩
  rw [← hc] at h10₁ h11₁ k
  obtain ⟨d, hd⟩ : ∃ d, d = (s.mem (at' S (Layout.oDigits + c))).toNat := ⟨_, rfl⟩
  rw [← hd] at h11₁ k
  have hd256 : d < 256 := by rw [hd]; exact (s.mem _).isLt
  rw [m₁, hv1, h11₁] at z₂ c₂
  have hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have hg₂ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s₂.gpr g = s.gpr g :=
    fun g h1 h2 h3 h4 h5 h6 => by rw [g₂, g₁ _ h1 h2 h3 h5 h6]
  have hd' : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hj' : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hd', hj'] at c₂
  rw [cmp_eq (by omega) (by omega)] at z₂
  refine WP.ite (decide (d = j)) z₂ (fun he => WP.block_nil ?_) (fun he => ?_)
  · have : ¬ j < d := by have := of_decide_eq_true he; omega
    exact k s₂ hg₂ (by rw [r₂, r₁]) (by rw [w₂, w₁]) (by simp only [this, ↓reduceIte, hm₂])
      (by rw [hm₂]; exact Frame.refl _ _)
  refine WP.ite (decide (d < j)) c₂ (fun hl => WP.block_nil ?_) (fun hl => ?_)
  · have : ¬ j < d := by have := of_decide_eq_true hl; omega
    exact k s₂ hg₂ (by rw [r₂, r₁]) (by rw [w₂, w₁]) (by simp only [this, ↓reduceIte, hm₂])
      (by rw [hm₂]; exact Frame.refl _ _)
  have hjd : j < d := by
    have h1 : ¬ d = j := of_decide_eq_false he
    have h2 : ¬ d < j := of_decide_eq_false hl
    omega
  have h := sigLane_ok (is := []) hn hk' (c := c) (by omega) (s := s₂) (by rw [g₂, hb₁]) (by rw [g₂, h10₁])
    (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h13])
    (by rw [w₂, w₁]; exact hw) (by rw [r₂, r₁]; exact hsr) hsfit hss hsL (Q := Q) fun s₃ g₃ r₃ w₃ v₃ f₃ =>
      WP.block_nil (k s₃ (fun g h1 h2 h3 h4 h5 h6 => by rw [g₃ _ h1 h4, hg₂ _ h1 h2 h3 h4 h5 h6])
        (by rw [r₃, r₂, r₁]) (by rw [w₃, w₂, w₁]) (by simp only [hjd, ↓reduceIte, v₃, hm₂]) (by rw [← hm₂]; exact f₃))
  rwa [List.append_nil] at h

/-- The first block of `stepBody`: each lane's hash address the step `j`
(variable 1). -/
theorem hash28_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {j : Nat} (hj : j < 2 ^ 32)
    {s : State} {S : Addr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (hv1 : s.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .r10 → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      (∀ k' < 4, bytesAt s'.mem (at' S (Layout.laneA k' + p.n + 28)) 4 = toByte j 4) →
      Frame ((List.range 4).map fun k' => ⟨at' S (Layout.laneA k' + p.n + 28), 4⟩) s.mem s'.mem → Q s') :
    WP isa (.block (.mov .r10 (.mem (Impl.SlhDsa.X86_64.Verify.xv 1)) :: (List.range 4).flatMap fun k' =>
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r10)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  rw [hadr]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  refine wp_movm (a := at' S (Layout.oVar 1 1)) (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hbx])
    (by rw [oVar11]; exact in_scr' hw (by omega)) fun s₀ u₀ => ?_
  rw [hv1] at u₀
  have hj' : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hin : ∀ (t : State) (o : Nat), t.gpr .rbx = S → t.wr = s.wr → o + 4 ≤ 2 ^ 16 →
      InRegions t.wr (t.gpr .rbx + BitVec.ofNat 64 o) 4 := fun t o h₁ h₂ ho => by
    rw [h₁, h₂]; exact in_scr hw ho
  have hb₀ : s₀.gpr .rbx = S := by rw [u₀.other _ (by decide), hbx]
  simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine setFieldR_ok (by decide) (by rw [u₀.gpr, hj']; exact hj) (hin s₀ _ hb₀ u₀.wr (by rw [eA]; omega))
    fun s₁ f₁ => ?_
  rw [hb₀, u₀.gpr, hj'] at f₁
  have hb₁ : s₁.gpr .rbx = S := by rw [f₁.gpr _ (by decide), hb₀]
  have h₁ : s₁.gpr .r10 = BitVec.ofNat 64 j := by rw [f₁.gpr _ (by decide), u₀.gpr]
  refine setFieldR_ok (by decide) (by rw [h₁, hj']; exact hj) (hin s₁ _ hb₁ (by rw [f₁.wr, u₀.wr]) (by rw [eA]; omega))
    fun s₂ f₂ => ?_
  rw [hb₁, h₁, hj'] at f₂
  have hb₂ : s₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  have h₂ : s₂.gpr .r10 = BitVec.ofNat 64 j := by rw [f₂.gpr _ (by decide), h₁]
  refine setFieldR_ok (by decide) (by rw [h₂, hj']; exact hj)
    (hin s₂ _ hb₂ (by rw [f₂.wr, f₁.wr, u₀.wr]) (by rw [eA]; omega)) fun s₃ f₃ => ?_
  rw [hb₂, h₂, hj'] at f₃
  have hb₃ : s₃.gpr .rbx = S := by rw [f₃.gpr _ (by decide), hb₂]
  have h₃ : s₃.gpr .r10 = BitVec.ofNat 64 j := by rw [f₃.gpr _ (by decide), h₂]
  have h := setFieldR_ok (is := []) (Q := Q) (by decide) (by rw [h₃, hj']; exact hj)
    (hin s₃ (Layout.laneA 3 + p.n + 28) hb₃ (by rw [f₃.wr, f₂.wr, f₁.wr, u₀.wr]) (by rw [eA]; omega)) fun s₄ f₄ => ?_
  · rwa [List.append_nil] at h
  rw [hb₃, h₃, hj'] at f₄
  refine WP.block_nil (k s₄ (fun g h1 h2 => by rw [f₄.gpr _ h1, f₃.gpr _ h1, f₂.gpr _ h1, f₁.gpr _ h1, u₀.other _ h2])
    (by rw [f₄.rd, f₃.rd, f₂.rd, f₁.rd, u₀.rd]) (by rw [f₄.wr, f₃.wr, f₂.wr, f₁.wr, u₀.wr]) (fun k' hk' => ?_) ?_)
  · have hd : ∀ a c : Nat, a ≠ c → a < 4 → c < 4 → ∀ r ∈ [(⟨S + BitVec.ofNat 64 (Layout.laneA c + p.n + 28), 4⟩ : Region)],
        Region.Disjoint ⟨at' S (Layout.laneA a + p.n + 28), 4⟩ r := fun a c h ha hc r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eA, eA]; exact Offset.disjoint S (by omega) (by omega) (by omega)
    have h3 : k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 := by omega
    rcases h3 with rfl | rfl | rfl | rfl
    · rw [bytesAt_frame f₄.frame (hd _ _ (by decide) (by decide) (by decide)) (by decide),
        bytesAt_frame f₃.frame (hd _ _ (by decide) (by decide) (by decide)) (by decide),
        bytesAt_frame f₂.frame (hd _ _ (by decide) (by decide) (by decide)) (by decide)]
      exact f₁.bytes
    · rw [bytesAt_frame f₄.frame (hd _ _ (by decide) (by decide) (by decide)) (by decide),
        bytesAt_frame f₃.frame (hd _ _ (by decide) (by decide) (by decide)) (by decide)]
      exact f₂.bytes
    · rw [bytesAt_frame f₄.frame (hd _ _ (by decide) (by decide) (by decide)) (by decide)]
      exact f₃.bytes
    · exact f₄.bytes
  · have hs : ∀ c < 4, ∀ r ∈ [(⟨S + BitVec.ofNat 64 (Layout.laneA c + p.n + 28), 4⟩ : Region)],
        ∃ r' ∈ (List.range 4).map (fun k' => (⟨at' S (Layout.laneA k' + p.n + 28), 4⟩ : Region)), Region.Sub r r' :=
      fun c hc r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩, fun _ h => h⟩
    rw [← u₀.mem]
    exact (f₁.frame.sub (hs 0 (by decide))).trans ((f₂.frame.sub (hs 1 (by decide))).trans
      ((f₃.frame.sub (hs 2 (by decide))).trans (f₄.frame.sub (hs 3 (by decide)))))

/-- A byte outside a frame's regions is unchanged. -/
theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {x : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨x, 1⟩ r) : m' x = m x := by
  have e := hf.bytes (R := ⟨x, 1⟩) hd (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
  simpa using e

theorem F_shake {p : Params} (hf : p.family = .shake) (pk : List Byte) (a : Adrs) (M : List Byte) :
    F p pk a M = shake256 (pk ++ a ++ M) p.n := by
  simp only [F, hf, shakeAdrs]

/-- The restores of a step: the state after the call `s₂`, and the lanes
below `K` done. -/
structure RInv (p : Params) (S sig : Addr) (c₀ j : Nat) (s₂ : State) (K : Nat) (u : State) : Prop where
  bx : u.gpr .rbx = S
  r13 : u.gpr .r13 = sig
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₂.gpr g
  rd : u.rd = s₂.rd
  wr : u.wr = s₂.wr
  v0 : u.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀
  v1 : u.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j
  frame : Frame ((List.range 4).map fun k => ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩) s₂.mem u.mem
  done : ∀ k < K, bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
    if j < (s₂.mem (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat then
      bytesAt s₂.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n
    else bytesAt s₂.mem (at' S (Layout.laneA k + p.n + 32)) p.n
  todo : ∀ k, K ≤ k → k < 4 →
    bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n = bytesAt s₂.mem (at' S (Layout.laneA k + p.n + 32)) p.n

/-- Lane values outside each other, the variables, the digits. -/
theorem lanesV_disj {p : Params} (hn : p.n ≤ 32) (S : Addr) {o l : Nat} (hol : o + l ≤ 2 ^ 16)
    (h : ∀ c < 4, o + l ≤ Layout.laneA c + p.n + 32 ∨ Layout.laneA c + 2 * p.n + 32 ≤ o) :
    ∀ r ∈ (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ : Region)),
      Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [List.mem_map, List.mem_range] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  have := h c hc
  have eA : Layout.laneA c = 3296 + 128 * c := rfl
  rw [eA] at this ⊢
  exact Offset.disjoint S (by omega) (by omega) (by omega)

/-- One lane's restore, in the restores of a step. -/
theorem rstep {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {S sig : Addr} {c₀ j K : Nat} {s₂ u : State} (hK : K < 4) (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s₂.wr) {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s₂.rd)
    (hsfit : sig.toNat + sL ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (hu : RInv p S sig c₀ j s₂ K u) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u', RInv p S sig c₀ j s₂ (K + 1) u' → WP isa rest u' Q) :
    WP isa (.seq (Impl.SlhDsa.X86_64.Verify.restoreLane p K) rest) u Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have hv8 : ∀ i, (⟨at' S (Layout.oVar 1 i), 8⟩ : Region).Contains (at' S (Layout.oVar 1 i)) (64 / 8) :=
    fun _ => Region.contains_self _ _
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun i => rfl
  have hc : min (c₀ + K) (p.len - 1) < p.len := by omega
  have hcn : min (c₀ + K) (p.len - 1) * p.n + p.n ≤ p.len * p.n := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
  refine WP.seq (restore_ok hn hlen1 hlen hK hc₀ hj hu.bx hu.r13 hu.v0 hu.v1 (by rw [hu.wr]; exact hw)
    (by rw [hu.rd]; exact hsr) hsfit hss hsL fun u' g' r' w' v' F' => k u' ?_)
  have hKd : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ Layout.laneA K + p.n + 32 ∨ Layout.laneA K + 2 * p.n + 32 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.laneA K + p.n + 32), p.n⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eA] at h₂ ⊢; exact Offset.disjoint S (by omega) (by omega) (by omega)
  -- the digit and the signature value, as they were after the call
  have hdig : u.mem (at' S (Layout.oDigits + min (c₀ + K) (p.len - 1))) =
      s₂.mem (at' S (Layout.oDigits + min (c₀ + K) (p.len - 1))) :=
    frame_at hu.frame (lanesV_disj hn32 S (l := 1) (by rw [oDigits_eq]; omega) fun c hc => by
      rw [oDigits_eq, eA]; omega)
  have hsig : bytesAt u.mem (sig + BitVec.ofNat 64 (min (c₀ + K) (p.len - 1) * p.n)) p.n =
      bytesAt s₂.mem (sig + BitVec.ofNat 64 (min (c₀ + K) (p.len - 1) * p.n)) p.n :=
    bytesAt_frame hu.frame (fun r hr => by
      simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨c, hc', rfl⟩ := hr
      exact (hss.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S (by rw [eA]; omega)))
      (by omega)
  refine ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.bx],
    by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.r13],
    fun g h1 h2 h3 h4 h5 h6 => by rw [g' _ h1 h2 h3 h4 h5 h6, hu.gpr _ h1 h2 h3 h4 h5 h6],
    by rw [r', hu.rd], by rw [w', hu.wr],
    by rw [F'.readW (hv8 0) (hKd (by rw [eV]; omega) (Or.inl (by rw [eV, eA]; omega))) (by decide), hu.v0],
    by rw [F'.readW (hv8 1) (hKd (by rw [eV]; omega) (Or.inl (by rw [eV, eA]; omega))) (by decide), hu.v1],
    hu.frame.trans (F'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨K, List.mem_range.mpr hK, rfl⟩, fun _ h => h⟩),
    fun k' hk' => ?_, fun k' hk₁ hk₂ => ?_⟩
  · by_cases he : k' = K
    · subst he
      rw [v', hdig, hsig, hu.todo k' (Nat.le_refl _) hK]
    · rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega)) (by omega), hu.done k' (by omega)]
  · rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega)) (by omega), hu.todo k' (by omega) hk₂]

/-- Step `j` of a group (`stepBody`): each lane's value one `F` further (at
the hash address `j`), or its signature value back if its digit is above
`j`; then `j + 1` in variable 1, ZF set after step 14. -/
theorem stepBody_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {t : State} {S sig : Addr} {idx c₀ j : Nat} {pkSeed a16 : List Byte} (hc₀ : c₀ + 4 < 2 ^ 31) (hj : j < 15)
    (hbx : t.gpr .rbx = S) (h13 : t.gpr .r13 = sig)
    (hv0 : t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hv1 : t.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p t.mem S pkSeed a16)
    (hfld : ∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
      toByte 0 4 ++ toByte idx 4 ++ toByte (min (c₀ + k) (p.len - 1)) 4)
    {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ t.rd) (hsfit : sig.toNat + sL ≤ 2 ^ 64)
    (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (hsb : Region.Disjoint ⟨sig, sL⟩ (below (t.gpr .rsp) stack))
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) → t'.rd = t.rd → t'.wr = t.wr →
      t'.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀ →
      t'.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 (j + 1) →
      t'.zf = some (decide (j + 1 = 15)) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
        bytesAt t.mem (at' S (Layout.laneA k + p.n + 16)) 12) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
        if j < (t.mem (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat then
          bytesAt t.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n
        else F p pkSeed (adrsOf a16 0 idx (min (c₀ + k) (p.len - 1)) j)
          (bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n)) →
      Frame (chFrame p S (t.gpr .rsp) stack) t.mem t'.mem → Q t') :
    WP isa (Impl.SlhDsa.X86_64.Verify.stepBody p f) t Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have hv8 : ∀ i, (⟨at' S (Layout.oVar 1 i), 8⟩ : Region).Contains (at' S (Layout.oVar 1 i)) (64 / 8) :=
    fun _ => Region.contains_self _ _
  have eV : ∀ i, Layout.oVar 1 i = 2576 + 8 * i := fun i => rfl
  -- what the hash addresses' stores leave
  have D28 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
      (∀ c < 4, o + l ≤ Layout.laneA c + p.n + 28 ∨ Layout.laneA c + p.n + 32 ≤ o) →
      ∀ r ∈ (List.range 4).map (fun k' => (⟨at' S (Layout.laneA k' + p.n + 28), 4⟩ : Region)),
        Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    have := h₂ c hc
    rw [eA] at this ⊢
    exact Offset.disjoint S (by omega) (by omega) (by omega)
  unfold Impl.SlhDsa.X86_64.Verify.stepBody
  refine WP.seq (hash28_ok hn (by omega) hbx hv1 hw fun s₁ g₁ r₁ w₁ b₁ F₁ => ?_)
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ (by decide) (by decide), hbx]
  have hsp₁ : s₁.gpr .rsp = t.gpr .rsp := g₁ _ (by decide) (by decide)
  have F₁c : Frame (changes p S ++ [below (t.gpr .rsp) stack]) t.mem s₁.mem := F₁.sub fun r hr => by
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact sub_changes hn32 S _ (Or.inl ⟨c, hc, by omega, by omega⟩)
  have henv₁ := Env.of_frame hn32 henv F₁c hstk
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₁.wr := by rw [w₁]; exact hw
  -- the call: the lanes `A`, messages of `2n + 32` bytes
  rw [ht]
  refine WP.seq (lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oA) (st := Layout.strideA)
    (len := 2 * p.n + 32) (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega_using [hn]) (by simp only [Layout.strideA]; omega)
    hb₁ hw₁ hS (by rw [hsp₁]; exact hstk) henv₁.rc fun s₂ r₂ w₂ g₂ o₂ _ F₂ => ?_)
  rw [hsp₁] at F₂
  have D2 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → 2400 ≤ o →
      (∀ c < 4, o + l ≤ Layout.laneA c + p.n + 32 ∨ Layout.laneA c + 2 * p.n + 32 ≤ o) →
      ∀ r ∈ lanesOut p S Layout.oA Layout.strideA ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (t.gpr .rsp) stack],
        Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₀ h₂ r hr => by
    simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
    · have := h₂ c hc
      rw [eA] at this
      exact Offset.disjoint S (by simp only [Layout.oA, Layout.strideA]; omega) (by omega)
        (by simp only [Layout.oA, Layout.strideA]; omega)
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hstk.sub_right (Offset.sub_base S h₁)).symm
  have hb₂ : s₂.gpr .rbx = S := by rw [g₂ _ (by decide), hb₁]
  have hfld₁ : ∀ k < 4, bytesAt s₁.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
      bytesAt t.mem (at' S (Layout.laneA k + p.n + 16)) 12 := fun k hk =>
    bytesAt_frame F₁ (D28 (by rw [eA]; omega) fun c hc => by rw [eA, eA]; omega) (by omega)
  have hfld₂ : ∀ k < 4, bytesAt s₂.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
      bytesAt t.mem (at' S (Layout.laneA k + p.n + 16)) 12 := fun k hk => by
    rw [bytesAt_frame F₂ (D2 (by rw [eA]; omega) (by rw [eA]; omega) fun c hc => by rw [eA, eA]; omega) (by omega),
      hfld₁ k hk]
  have hval₁ : ∀ k < 4, bytesAt s₁.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n := fun k hk =>
    bytesAt_frame F₁ (D28 (by rw [eA]; omega) fun c hc => by rw [eA, eA]; omega) (by omega)
  -- each lane's output, `F` at the address of step `j`
  have hout : ∀ k < 4, bytesAt s₂.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      F p pkSeed (adrsOf a16 0 idx (min (c₀ + k) (p.len - 1)) j) (bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n) := by
    intro k hk
    have o := o₂ k hk
    rw [show Layout.oA + Layout.strideA * k = Layout.laneA k from rfl] at o
    rw [o, F_shake hfam]
    refine congrArg (shake256 · p.n) ?_
    rw [show 2 * p.n + 32 = p.n + (16 + (12 + (4 + p.n))) by omega, bytesAt_split2, bytesAt_split2, bytesAt_split2,
      bytesAt_split2, show Layout.laneA k + p.n + 16 + 12 = Layout.laneA k + p.n + 28 by omega,
      show Layout.laneA k + p.n + 28 + 4 = Layout.laneA k + p.n + 32 by omega]
    rw [show S + BitVec.ofNat 64 (Layout.laneA k) = at' S (Layout.laneA k) from rfl, henv₁.seedA k hk,
      show S + BitVec.ofNat 64 (Layout.laneA k + p.n) = at' S (Layout.laneA k + p.n) from rfl, henv₁.adrsA k hk,
      show S + BitVec.ofNat 64 (Layout.laneA k + p.n + 16) = at' S (Layout.laneA k + p.n + 16) from rfl,
      hfld₁ k hk, hfld k hk,
      show S + BitVec.ofNat 64 (Layout.laneA k + p.n + 28) = at' S (Layout.laneA k + p.n + 28) from rfl, b₁ k hk,
      show S + BitVec.ofNat 64 (Layout.laneA k + p.n + 32) = at' S (Layout.laneA k + p.n + 32) from rfl, hval₁ k hk]
    simp only [adrsOf, List.append_assoc]
  -- the variables
  have hv0₂ : s₂.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀ := by
    rw [F₂.readW (hv8 0) (D2 (by rw [eV]; omega) (by rw [eV]; omega) fun c hc => by rw [eV, eA]; omega) (by decide),
      F₁.readW (hv8 0) (D28 (by rw [eV]; omega) fun c hc => by rw [eV, eA]; omega) (by decide), hv0]
  have hv1₂ : s₂.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j := by
    rw [F₂.readW (hv8 1) (D2 (by rw [eV]; omega) (by rw [eV]; omega) fun c hc => by rw [eV, eA]; omega) (by decide),
      F₁.readW (hv8 1) (D28 (by rw [eV]; omega) fun c hc => by rw [eV, eA]; omega) (by decide), hv1]
  -- the digits and the signature, as they were
  have hdig : ∀ c < 128, s₂.mem (at' S (Layout.oDigits + c)) = t.mem (at' S (Layout.oDigits + c)) := fun c hc => by
    rw [frame_at F₂ (D2 (l := 1) (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega)
        fun c' hc' => by rw [oDigits_eq, eA]; omega),
      frame_at F₁ (D28 (l := 1) (by rw [oDigits_eq]; omega) fun c' hc' => by rw [oDigits_eq, eA]; omega)]
  have hsig : ∀ c < p.len, bytesAt s₂.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n =
      bytesAt t.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n := fun c hc => by
    have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    have hsub : Region.Sub ⟨sig + BitVec.ofNat 64 (c * p.n), p.n⟩ ⟨sig, sL⟩ := Offset.sub_base sig (by omega)
    rw [bytesAt_frame F₂ (fun r hr => ?_) (by omega), bytesAt_frame F₁ (fun r hr => ?_) (by omega)]
    · simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨c', hc', rfl⟩ := hr
      exact (hss.sub_left hsub).sub_right (Offset.sub_base S (by rw [eA]; omega))
    · simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨c', hc', rfl⟩ | rfl | rfl | rfl
      · exact (hss.sub_left hsub).sub_right (Offset.sub_base S (by simp only [Layout.oA, Layout.strideA]; omega))
      · exact (hss.sub_left hsub).sub_right (Region.sub_prefix (by decide))
      · exact (hss.sub_left hsub).sub_right (Offset.sub_base S (by decide))
      · exact hsb.sub_left hsub
  -- the restores
  have hR₀ : RInv p S sig c₀ j s₂ 0 s₂ :=
    ⟨hb₂, by rw [g₂ _ (by decide), g₁ _ (by decide) (by decide), h13], fun _ _ _ _ _ _ _ => rfl, rfl, rfl,
      hv0₂, hv1₂, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  have hw₂ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₂.wr := by rw [w₂]; exact hw₁
  have hsr₂ : (⟨sig, sL⟩ : Region) ∈ s₂.rd := by rw [r₂, r₁]; exact hsr
  refine rstep hn hlen1 hlen (by decide) hc₀ (by omega) hw₂ hsr₂ hsfit hss hsL hR₀ fun u₁ hu₁ => ?_
  refine rstep hn hlen1 hlen (by decide) hc₀ (by omega) hw₂ hsr₂ hsfit hss hsL hu₁ fun u₂ hu₂ => ?_
  refine rstep hn hlen1 hlen (by decide) hc₀ (by omega) hw₂ hsr₂ hsfit hss hsL hu₂ fun u₃ hu₃ => ?_
  refine rstep hn hlen1 hlen (by decide) hc₀ (by omega) hw₂ hsr₂ hsfit hss hsL hu₃ fun u hu => ?_
  -- `j + 1`
  have hxv : u.gpr .rbx = S := hu.bx
  refine wp_movm (a := at' S (Layout.oVar 1 1)) (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hxv])
    (by rw [hu.rd, hu.wr, w₂, w₁, eV]; exact in_scr' hw (by omega)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  have hb₆ : s₆.gpr .rbx = S := by rw [u₆.other _ (by decide), u₅.other _ (by decide), hxv]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 1 1))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hb₆])
    (by rw [u₆.wr, u₅.wr, hu.wr, w₂, w₁, eV]; exact in_scr hw (by omega)) fun s₇ g₇ m₇ r₇ w₇ => ?_
  refine Levels.wp_cmpi fun s₈ g₈ m₈ r₈ w₈ z₈ => WP.block_nil ?_
  have hrax : s₆.gpr .rax = BitVec.ofNat 64 (j + 1) := by
    rw [u₆.gpr, u₅.gpr, hu.v1, sx1']; exact (BitVec.ofNat_add j 1).symm
  have hm₈ : s₈.mem = u.mem.writeW (at' S (Layout.oVar 1 1)) (BitVec.ofNat 64 (j + 1)) := by
    rw [m₈, m₇, hrax, u₆.mem, u₅.mem]
  have F₈ : Frame [⟨at' S (Layout.oVar 1 1), 8⟩] u.mem s₈.mem := by
    rw [hm₈]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have D8 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 2584 ∨ 2592 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.oVar 1 1), 8⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [eV]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hne : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by decide
  refine k s₈ (fun r hr => ?_) (by rw [r₈, r₇, u₆.rd, u₅.rd, hu.rd, r₂, r₁])
    (by rw [w₈, w₇, u₆.wr, u₅.wr, hu.wr, w₂, w₁]) ?_ (by rw [hm₈]; exact Mem.readW_writeW_self64 _ _ _) ?_
    (fun k' hk' => ?_) (fun k' hk' => ?_) ?_
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hne r hr
    rw [g₈, g₇, u₆.other _ h₁, u₅.other _ h₁, hu.gpr _ h₁ h₂ h₃ h₄ h₅ h₆, g₂ r hr, g₁ _ h₁ h₅]
  · rw [F₈.readW (hv8 0) (D8 (by rw [eV]; omega) (by rw [eV]; omega)) (by decide), hu.v0]
  · rw [z₈, g₇, hrax, show BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 15 by decide,
      cmp_eq (by omega) (by omega)]
  · rw [bytesAt_frame F₈ (D8 (by rw [eA]; omega) (by rw [eA]; omega)) (by omega),
      bytesAt_frame hu.frame (lanesV_disj hn32 S (by rw [eA]; omega) fun c hc => by rw [eA, eA]; omega) (by omega),
      hfld₂ k' hk']
  · have hc : min (c₀ + k') (p.len - 1) < 128 := by omega
    rw [bytesAt_frame F₈ (D8 (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), hu.done k' hk', hdig _ hc,
      hsig _ (by omega), hout k' hk']
  · have h1 : Frame (chFrame p S (t.gpr .rsp) stack) t.mem s₁.mem := F₁.sub fun r hr => by
      simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨c, hc, rfl⟩ := hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
        Offset.sub S (by omega) (by rw [eA]; simp only [Layout.strideA]; omega)⟩
    have h2 : Frame (chFrame p S (t.gpr .rsp) stack) s₁.mem s₂.mem := F₂.sub fun r hr => by
      simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
          Offset.sub S (by simp only [Layout.laneA]; omega)
            (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
    have h3 : Frame (chFrame p S (t.gpr .rsp) stack) s₂.mem u.mem := hu.frame.sub fun r hr => by
      simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨c, hc, rfl⟩ := hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
        Offset.sub S (by omega) (by rw [eA]; simp only [Layout.strideA]; omega)⟩
    have h4 : Frame (chFrame p S (t.gpr .rsp) stack) u.mem s₈.mem := F₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
        Offset.sub S (by simp only [eV]; omega) (by simp only [eV]; omega)⟩
    exact h1.trans (h2.trans (h3.trans h4))

/-- A verification lane's value after the steps from `t₀` to `j`. -/
def runTo (p : Params) (pkSeed : List Byte) (adrs : Adrs) (X : List Byte) (d t₀ j : Nat) : List Byte :=
  (List.range (j - t₀)).foldl (fun v j' => if t₀ + j' < d then X else F p pkSeed (setHashAddress adrs (t₀ + j')) v) X

theorem runTo_succ (p : Params) (pkSeed : List Byte) (adrs : Adrs) (X : List Byte) {d t₀ j : Nat} (h : t₀ ≤ j) :
    runTo p pkSeed adrs X d t₀ (j + 1) =
      if j < d then X else F p pkSeed (setHashAddress adrs j) (runTo p pkSeed adrs X d t₀ j) := by
  simp only [runTo]
  rw [show j + 1 - t₀ = (j - t₀) + 1 by omega, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, show t₀ + (j - t₀) = j by omega]

/-- The steps of a group, from its first step `t₀ < 15` (variable 1) to 14:
each lane's value `runTo` 15 of its signature value. -/
theorem stepLoop_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {idx c₀ t₀ : Nat} {pkSeed a16 : List Byte} (hc₀ : c₀ + 4 < 2 ^ 31) (ht₀ : t₀ < 15)
    (hbx : s.gpr .rbx = S) (h13 : s.gpr .r13 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hv1 : s.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 t₀)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hfld : ∀ k < 4, bytesAt s.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
      toByte 0 4 ++ toByte idx 4 ++ toByte (min (c₀ + k) (p.len - 1)) 4)
    {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd) (hsfit : sig.toNat + sL ≤ 2 ^ 64)
    (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (hsb : Region.Disjoint ⟨sig, sL⟩ (below (s.gpr .rsp) stack))
    (hval : ∀ k < 4, bytesAt s.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n)
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr →
      t'.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀ →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
        bytesAt s.mem (at' S (Layout.laneA k + p.n + 16)) 12) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
        runTo p pkSeed (adrsOf a16 0 idx (min (c₀ + k) (p.len - 1)) 0)
          (bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n)
          (s.mem (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat t₀ 15) →
      Frame (chFrame p S (s.gpr .rsp) stack) s.mem t'.mem → Q t') :
    WP isa (.loop (Impl.SlhDsa.X86_64.Verify.stepBody p f) .ne) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have ha16 : a16.length = 16 := by rw [← henv.adrsA 0 (by decide)]; exact bytesAt_length' _ _ _
  -- what a frame of `chFrame` leaves: the digits, the signature
  have hdig : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack) s.mem m → ∀ c < 128,
      m (at' S (Layout.oDigits + c)) = s.mem (at' S (Layout.oDigits + c)) := fun hf c hc =>
    frame_at hf (chFrame_disj hn32 hstk (l := 1) (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega))
  have hsig : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack) s.mem m → ∀ c < p.len,
      bytesAt m (sig + BitVec.ofNat 64 (c * p.n)) p.n = bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n :=
    fun hf c hc => by
      have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
      have hsub : Region.Sub ⟨sig + BitVec.ofNat 64 (c * p.n), p.n⟩ ⟨sig, sL⟩ := Offset.sub_base sig (by omega)
      exact bytesAt_frame hf (chFrame_disj' hn32 (hss.sub_left hsub) (hsb.sub_left hsub)) (by omega)
  let Inv : Nat → State → Prop := fun m t => ∃ j, m = 15 - j ∧ t₀ ≤ j ∧ j < 15 ∧
    (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀ ∧
    t.mem.readW (at' S (Layout.oVar 1 1)) 64 = BitVec.ofNat 64 j ∧
    (∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
      bytesAt s.mem (at' S (Layout.laneA k + p.n + 16)) 12) ∧
    (∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      runTo p pkSeed (adrsOf a16 0 idx (min (c₀ + k) (p.len - 1)) 0)
        (bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n)
        (s.mem (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat t₀ j) ∧
    Frame (chFrame p S (s.gpr .rsp) stack) s.mem t.mem
  have hbxcs : Reg.rbx ∈ calleeSaved := by decide
  have h13cs : Reg.r13 ∈ calleeSaved := by decide
  have hspcs : Reg.rsp ∈ calleeSaved := by decide
  refine WP.loop (M := isa) Inv (fun m t ⟨j, hm, hj₀, hj, gt, rt, wt, v0t, v1t, ft, lt, Ft⟩ => ?_) (15 - t₀) s
    ⟨t₀, rfl, Nat.le_refl _, ht₀, fun _ _ => rfl, rfl, rfl, hv0, hv1, fun _ _ => rfl,
      fun k hk => by rw [hval k hk]; simp only [runTo, Nat.sub_self, List.range_zero, List.foldl_nil], Frame.refl _ _⟩
  have hsp : t.gpr .rsp = s.gpr .rsp := gt _ hspcs
  have henvt := Env.of_frame hn32 henv (Ft.sub (chFrame_sub p S _ stack)) hstk
  refine stepBody_ok T ht hn hfam hlen1 hlen hst hs63 (idx := idx) hc₀ hj (by rw [gt _ hbxcs, hbx])
    (by rw [gt _ h13cs, h13]) v0t v1t (by rw [wt]; exact hw) hS (by rw [hsp]; exact hstk) henvt
    (fun k hk => by rw [ft k hk, hfld k hk]) (by rw [rt]; exact hsr) hsfit hss hsL (by rw [hsp]; exact hsb)
    fun t' g' r' w' v0' v1' z' f' l' F' => ?_
  rw [hsp] at F'
  have Ft' := Ft.trans F'
  have hval' : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      runTo p pkSeed (adrsOf a16 0 idx (min (c₀ + k) (p.len - 1)) 0)
        (bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n)
        (s.mem (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat t₀ (j + 1) := fun k hk => by
    rw [l' k hk, runTo_succ _ _ _ _ hj₀, hdig Ft _ (by omega), hsig Ft _ (by omega), lt k hk,
      setHashAddress_adrsOf ha16]
  by_cases hlast : j + 1 = 15
  · refine Or.inl ⟨by show t'.zf.map (!·) = some false; rw [z', decide_eq_true hlast]; rfl, ?_⟩
    exact k t' (fun r hr => by rw [g' r hr, gt r hr]) (by rw [r', rt]) (by rw [w', wt]) v0'
      (fun k hk => by rw [f' k hk, ft k hk]) (fun k hk => by rw [hval' k hk, hlast]) Ft'
  · refine Or.inr ⟨by show t'.zf.map (!·) = some true; rw [z', decide_eq_false hlast]; rfl, 15 - (j + 1),
      by omega, j + 1, rfl, by omega, by omega, fun r hr => by rw [g' r hr, gt r hr], by rw [r', rt], by rw [w', wt],
      v0', v1', fun k hk => by rw [f' k hk, ft k hk], hval', Ft'⟩

/-- The least of 15 and the digits of the group's first `K` lanes. -/
def dmin (p : Params) (m : Mem) (S : Addr) (c₀ : Nat) : Nat → Nat
  | 0 => 15
  | K + 1 => min (dmin p m S c₀ K) (m (at' S (Layout.oDigits + min (c₀ + K) (p.len - 1)))).toNat

theorem dmin_le (p : Params) (m : Mem) (S : Addr) (c₀ : Nat) : ∀ K, dmin p m S c₀ K ≤ 15
  | 0 => Nat.le_refl _
  | K + 1 => Nat.le_trans (Nat.min_le_left _ _) (dmin_le p m S c₀ K)

theorem dmin_le_digit (p : Params) (m : Mem) (S : Addr) (c₀ : Nat) :
    ∀ K, ∀ k < K, dmin p m S c₀ K ≤ (m (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | K + 1, k, h => by
    simp only [dmin]
    by_cases e : k = K
    · subst e; exact Nat.min_le_right _ _
    · exact Nat.le_trans (Nat.min_le_left _ _) (dmin_le_digit p m S c₀ K k (by omega))

/-- The regions `chainLanes` writes. -/
def initR (p : Params) (S : Addr) : List Region :=
  (List.range 4).map (fun k => ⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩) ++ [⟨at' S (Layout.oVar 1 2), 8⟩]

/-- `chainLanes` after the lanes below `K`. -/
structure LInv (p : Params) (S sig : Addr) (idx c₀ : Nat) (s₀ : State) (K : Nat) (u : State) : Prop where
  bx : u.gpr .rbx = S
  r12 : u.gpr .r12 = BitVec.ofNat 64 idx
  r13 : u.gpr .r13 = sig
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₀.gpr g
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  v0 : u.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀
  v2 : u.mem.readW (at' S (Layout.oVar 1 2)) 64 = BitVec.ofNat 64 (dmin p s₀.mem S c₀ K)
  frame : Frame (initR p S) s₀.mem u.mem
  done : ∀ k < K, LaneInit p S k idx (min (c₀ + k) (p.len - 1))
    (bytesAt s₀.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n) u.mem

/-- A part of `scratch` outside the lanes `A` and the variables, outside `initR`. -/
theorem initR_disj {p : Params} (hn : p.n ≤ 32) (S : Addr) {o l : Nat} (h₁ : o + l ≤ 2 ^ 16)
    (h₂ : (∀ c < 4, o + l ≤ Layout.laneA c + p.n + 16 ∨ Layout.laneA c + 2 * p.n + 32 ≤ o) ∧ (o + l ≤ 2592 ∨ 2600 ≤ o)) :
    ∀ r ∈ initR p S, Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [initR, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with ⟨c, hc, rfl⟩ | rfl
  · have := h₂.1 c hc
    have eA : Layout.laneA c = 3296 + 128 * c := rfl
    rw [eA] at this ⊢
    exact Offset.disjoint S (by omega) (by omega) (by omega)
  · rw [oVar12]; exact Offset.disjoint S (by omega) (by omega) (by omega)

/-- One lane of `chainLanes`. -/
theorem lstep {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {S sig : Addr} {idx c₀ K : Nat} {s₀ u : State} (hK : K < 4) (hc₀ : c₀ + 4 < 2 ^ 31) (hidx : idx < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s₀.wr) {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s₀.rd)
    (hsfit : sig.toNat + sL ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (hu : LInv p S sig idx c₀ s₀ K u) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', LInv p S sig idx c₀ s₀ (K + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.chainOf p K ++
      setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 0 ++
      setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
      Impl.SlhDsa.X86_64.Verify.chainSig p ++
      Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
      ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63,
        .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .r11),
        .alu .xor .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .and .rax (.reg .rdx),
        .alu .xor .rax (.reg .r11), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] : List Instr)) ++ is)) u Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have hc : min (c₀ + K) (p.len - 1) < p.len := by omega
  have hcn : min (c₀ + K) (p.len - 1) * p.n + p.n ≤ p.len * p.n := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
  refine laneInit_ok hn hlen1 hlen hK hc₀ (by have := dmin_le p s₀.mem S c₀ K; omega) hidx hu.bx hu.r12 hu.r13 hu.v0
    hu.v2 (by rw [hu.wr]; exact hw) (by rw [hu.rd]; exact hsr) hsfit hss hsL fun u' g' r' w' li v2' F' => k u' ?_
  have hKd : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
      (o + l ≤ Layout.laneA K + p.n + 16 ∨ Layout.laneA K + 2 * p.n + 32 ≤ o) → (o + l ≤ 2592 ∨ 2600 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.laneA K + p.n + 16), 16 + p.n⟩ : Region), ⟨at' S (Layout.oVar 1 2), 8⟩],
        Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ h₃ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [eA] at h₂ ⊢; exact Offset.disjoint S (by omega) (by omega) (by omega)
    · rw [oVar12]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hdig : u.mem (at' S (Layout.oDigits + min (c₀ + K) (p.len - 1))) =
      s₀.mem (at' S (Layout.oDigits + min (c₀ + K) (p.len - 1))) :=
    frame_at hu.frame (initR_disj hn32 S (l := 1) (by rw [oDigits_eq]; omega)
      ⟨fun c hc => by rw [oDigits_eq, eA]; omega, by rw [oDigits_eq]; omega⟩)
  have hsig : bytesAt u.mem (sig + BitVec.ofNat 64 (min (c₀ + K) (p.len - 1) * p.n)) p.n =
      bytesAt s₀.mem (sig + BitVec.ofNat 64 (min (c₀ + K) (p.len - 1) * p.n)) p.n :=
    bytesAt_frame hu.frame (fun r hr => by
      simp only [initR, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
      rcases hr with ⟨c', hc', rfl⟩ | rfl
      · exact (hss.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S (by rw [eA]; omega))
      · exact (hss.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S (by rw [oVar12]; omega)))
      (by omega)
  refine ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.bx],
    by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.r12],
    by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.r13],
    fun g h1 h2 h3 h4 h5 h6 => by rw [g' _ h1 h2 h3 h4 h5 h6, hu.gpr _ h1 h2 h3 h4 h5 h6],
    by rw [r', hu.rd], by rw [w', hu.wr],
    by rw [F'.readW (Region.contains_self _ _) (hKd (by rw [oVar10]; omega) (Or.inl (by rw [oVar10, eA]; omega))
      (by rw [oVar10]; omega)) (by decide), hu.v0],
    by rw [v2', hdig]; rfl,
    hu.frame.trans (F'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨K, List.mem_range.mpr hK, rfl⟩), fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩),
    fun k' hk' => ?_⟩
  by_cases he : k' = K
  · subst he; rw [← hsig]; exact li
  · have d := hu.done k' (by omega)
    exact ⟨by rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega) (Or.inr (by rw [eA]; omega)))
        (by omega)]; exact d.fields,
      by rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega) (Or.inr (by rw [eA]; omega)))
        (by omega)]; exact d.value⟩

/-- `chainLanes`: the group's four lanes set up, and their least digit (and
15) in variable 2. -/
theorem chainLanes_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    {S sig : Addr} {idx c₀ : Nat} {s : State} (hc₀ : c₀ + 4 < 2 ^ 31) (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + sL ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    {Q : State → Prop} (k : ∀ u, LInv p S sig idx c₀ s 4 u → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.chainLanes p)) s Q := by
  have e : Impl.SlhDsa.X86_64.Verify.chainLanes p =
      [.mov32 .rax (.imm 15), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] ++
      ((fun K => Impl.SlhDsa.X86_64.Verify.chainOf p K ++
        setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 0 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        Impl.SlhDsa.X86_64.Verify.chainSig p ++
        Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
        ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63,
          .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .r11),
          .alu .xor .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .and .rax (.reg .rdx),
          .alu .xor .rax (.reg .r11), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] : List Instr)) 0 ++
      ((fun K => Impl.SlhDsa.X86_64.Verify.chainOf p K ++
        setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 0 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        Impl.SlhDsa.X86_64.Verify.chainSig p ++
        Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
        ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63,
          .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .r11),
          .alu .xor .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .and .rax (.reg .rdx),
          .alu .xor .rax (.reg .r11), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] : List Instr)) 1 ++
      ((fun K => Impl.SlhDsa.X86_64.Verify.chainOf p K ++
        setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 0 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        Impl.SlhDsa.X86_64.Verify.chainSig p ++
        Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
        ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63,
          .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .r11),
          .alu .xor .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .and .rax (.reg .rdx),
          .alu .xor .rax (.reg .r11), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] : List Instr)) 2 ++
      ((fun K => Impl.SlhDsa.X86_64.Verify.chainOf p K ++
        setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 0 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        Impl.SlhDsa.X86_64.Verify.chainSig p ++
        Impl.SlhDsa.X86_64.copyWords .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8) ++
        ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .sub .rax (.reg .r11), .shift .shr .rax 63,
          .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .r11),
          .alu .xor .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 2)), .alu .and .rax (.reg .rdx),
          .alu .xor .rax (.reg .r11), .store (Impl.SlhDsa.X86_64.Verify.xv 2) .rax] : List Instr)) 3 ++ [])))) := by
    simp only [Impl.SlhDsa.X86_64.Verify.chainLanes, List.range, List.range.loop, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  rw [e]
  refine wp_mov32i fun s₁ u₁ => Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 1 2))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.wr, oVar12]; exact in_scr hw (by omega)) fun s₂ g₂ m₂ r₂ w₂ => ?_
  have hm₂ : s₂.mem = s.mem.writeW (at' S (Layout.oVar 1 2)) (BitVec.ofNat 64 15) := by
    rw [m₂, u₁.gpr, u₁.mem]; rfl
  have F₂ : Frame (initR p S) s.mem s₂.mem := by
    rw [hm₂]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
  have hL₀ : LInv p S sig idx c₀ s 0 s₂ := by
    refine ⟨by rw [g₂, u₁.other _ (by decide), hbx], by rw [g₂, u₁.other _ (by decide), h12],
      by rw [g₂, u₁.other _ (by decide), h13], fun g h1 _ _ _ _ _ => by rw [g₂, u₁.other _ h1], by rw [r₂, u₁.rd],
      by rw [w₂, u₁.wr], ?_, by rw [hm₂, Mem.readW_writeW_self64]; rfl, F₂, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    rw [hm₂, Mem.readW_writeW_sep (by
      rw [oVar10, oVar12]
      exact Offset.sep S (Or.inl (by decide)) (by decide) (by decide)) (by decide), hv0]
  refine lstep hn hlen1 hlen (by decide) hc₀ hidx hw hsr hsfit hss hsL hL₀ fun u₁ hu₁ => ?_
  refine lstep hn hlen1 hlen (by decide) hc₀ hidx hw hsr hsfit hss hsL hu₁ fun u₂ hu₂ => ?_
  refine lstep hn hlen1 hlen (by decide) hc₀ hidx hw hsr hsfit hss hsL hu₂ fun u₃ hu₃ => ?_
  exact lstep hn hlen1 hlen (by decide) hc₀ hidx hw hsr hsfit hss hsL hu₃ fun u hu => WP.block_nil (k u hu)

/-- Lane `k`'s end copied to chain `c`'s place in lane 0 of `B`'s message. -/
theorem endLane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    (hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB)
    {k' c₀ : Nat} (hk' : k' < 4) (hc₀ : c₀ + 4 < 2 ^ 31) {s : State} {S : Addr} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneB 0 + p.n + 32 + min (c₀ + k') (p.len - 1) * p.n)) p.n =
        bytesAt s.mem (at' S (Layout.laneA k' + p.n + 32)) p.n →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 32 + min (c₀ + k') (p.len - 1) * p.n), p.n⟩] s.mem s'.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.chainOf p k' ++ ([.mov .rdx (.reg .r10)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      Impl.SlhDsa.X86_64.copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
        (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  have eA : Layout.laneA k' = 3296 + 128 * k' := rfl
  have eB : Layout.laneB 0 = 3808 := rfl
  have hsB : Layout.strideB = 2208 := rfl
  rw [hmsg]
  obtain ⟨c, hc⟩ : ∃ c, c = min (c₀ + k') (p.len - 1) := ⟨_, rfl⟩
  rw [← hc] at k
  have hcl : c < p.len := by omega
  have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hcl
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine chainOf_ok hlen1 hlen (by omega) hbx hv0 hw fun s₁ g₁ m₁ r₁ w₁ h10₁ _ => ?_
  rw [← hc] at h10₁
  refine wp_mov fun s₂ u₂ => Levels.mulN_ok hn (r := .rdx) (tmp := .rcx) (by decide) fun s₃ h₃ g₃ m₃ r₃ w₃ => ?_
  refine Levels.wp_add fun s₄ u₄ => WP.block_append ?_
  have hb₄ : s₄.gpr .rbx = S := by
    rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hdx : s₄.gpr .rdx = S + BitVec.ofNat 64 (c * p.n) := by
    rw [u₄.gpr, h₃, u₂.gpr, h10₁, g₃ _ (by decide) (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx, BitVec.add_comm, ← BitVec.ofNat_mul]
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₄.wr := by rw [u₄.wr, w₃, u₂.wr, w₁]; exact hw
  refine WP.mono (Levels.copy_ok (S := S) (t := .rdx) (sr := .rbx) (by decide) (by decide) (a := c * p.n) (b := 0)
    (d₁ := Layout.laneA k' + (p.n + 32)) (d₂ := Layout.laneB 0 + (p.n + 32)) (p.n / 8) s₄ hdx
    (by rw [hb₄]; exact Levels.scr0 S) hw₄ (by omega) (by rw [eB]; omega) (by rw [eA, eB]; omega))
    fun s₅ ⟨g₅, r₅, w₅, c₅, f₅⟩ => ?_
  have ea : at' S (Layout.laneB 0 + p.n + 32 + c * p.n) = S + BitVec.ofNat 64 (c * p.n + (Layout.laneB 0 + (p.n + 32))) := by
    rw [at']; congr 2; omega
  refine k s₅ (fun g h1 h2 h3 h4 h5 => ?_) (by rw [r₅, u₄.rd, r₃, u₂.rd, r₁]) (by rw [w₅, u₄.wr, w₃, u₂.wr, w₁])
    ?_ (by rw [ea, ← hm₄]; rw [e8] at f₅; exact f₅)
  · rw [g₅ _ h1, u₄.other _ h3, g₃ _ h3 h2, u₂.other _ h3, g₁ _ h1 h2 h3 h4 h5]
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [ea, add_add, c₅ i (by omega), hm₄, at', Nat.zero_add, add_add,
      show Layout.laneA k' + (p.n + 32) + i = Layout.laneA k' + p.n + 32 + i by omega]

/-- `cmp r64, imm32`, setting ZF and CF. -/
theorem wp_cmpi_cf {d : Reg} {v : BitVec 32} {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

/-- Chunks `c` and `c'` of `n` bytes, at `o`, apart. -/
theorem chunk_disj (S : Addr) {o n c c' : Nat} (h : c ≠ c') (hb : o + 128 * n ≤ 2 ^ 16) (hc : c < 128) (hc' : c' < 128) :
    Region.Disjoint ⟨at' S (o + c * n), n⟩ ⟨at' S (o + c' * n), n⟩ := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : c * n + n ≤ c' * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h
    have : c' * n + n ≤ 128 * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc'
    exact Offset.disjoint S (by omega) (by omega) (by omega)
  · have : c' * n + n ≤ c * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h
    have : c * n + n ≤ 128 * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    exact Offset.disjoint S (by omega) (by omega) (by omega)

/-- The ends of a group after the lanes below `K`. -/
structure EInv (p : Params) (S : Addr) (c₀ : Nat) (u₀ : State) (V : Nat → List Byte) (K : Nat) (u : State) : Prop where
  bx : u.gpr .rbx = S
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → g ≠ .r11 → u.gpr g = u₀.gpr g
  rd : u.rd = u₀.rd
  wr : u.wr = u₀.wr
  v0 : u.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀
  frame : Frame [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩] u₀.mem u.mem
  ends : ∀ c < p.len, bytesAt u.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
    if c₀ ≤ c ∧ c < c₀ + K then V c else bytesAt u₀.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n

/-- One lane's end. -/
theorem estep {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    (hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB)
    {S : Addr} {c₀ K : Nat} {u₀ u : State} {V : Nat → List Byte} (hK : K < 4) (hc₀ : c₀ < p.len)
    (hc₀' : c₀ + 4 < 2 ^ 31) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u₀.wr)
    (hval : ∀ k < 4, bytesAt u₀.mem (at' S (Layout.laneA k + p.n + 32)) p.n = V (min (c₀ + k) (p.len - 1)))
    (hu : EInv p S c₀ u₀ V K u) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', EInv p S c₀ u₀ V (K + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.chainOf p K ++ ([.mov .rdx (.reg .r10)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      Impl.SlhDsa.X86_64.copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
        (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++ is)) u Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have eB : Layout.laneB 0 = 3808 := rfl
  have hsB : Layout.strideB = 2208 := rfl
  have h128 : 128 * p.n ≤ 4096 := by omega
  refine endLane_ok hn hlen1 hlen hlB hK hc₀' hu.bx hu.v0 (by rw [hu.wr]; exact hw) fun u' g' r' w' e' F' => k u' ?_
  obtain ⟨c, hc⟩ : ∃ c, c = min (c₀ + K) (p.len - 1) := ⟨_, rfl⟩
  rw [← hc] at e' F'
  have hcl : c < p.len := by omega
  have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hcl
  have hln : p.len * p.n ≤ 128 * p.n := Nat.mul_le_mul_right _ hlen
  -- lane `K`'s value, as it was
  have hvK : bytesAt u.mem (at' S (Layout.laneA K + p.n + 32)) p.n = V c := by
    rw [bytesAt_frame hu.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eA, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega), hval K hK, hc]
  refine ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide), hu.bx],
    fun g h1 h2 h3 h4 h5 => by rw [g' _ h1 h2 h3 h4 h5, hu.gpr _ h1 h2 h3 h4 h5], by rw [r', hu.rd], by rw [w', hu.wr],
    by
      rw [F'.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [oVar10, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), hu.v0],
    hu.frame.trans (F'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩),
    fun c' hc' => ?_⟩
  by_cases he : c' = c
  · subst he
    rw [e', hvK, ite_eq_left (by omega)]
  · rw [bytesAt_frame F' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact chunk_disj S he (by rw [eB]; omega) (by omega) (by omega)) (by omega), hu.ends c' hc']
    by_cases h1 : c₀ ≤ c' ∧ c' < c₀ + K
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- The ends of a group (the last block of `chainGroup`): each lane's value
to its chain's place in lane 0 of `B`'s message; then `c₀ + 4` in variable
0, CF set while below `len`. -/
theorem ends_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    (hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB)
    {S : Addr} {c₀ : Nat} {u₀ : State} {V : Nat → List Byte} (hc₀ : c₀ < p.len)
    (hbx : u₀.gpr .rbx = S) (hv0 : u₀.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u₀.wr)
    (hval : ∀ k < 4, bytesAt u₀.mem (at' S (Layout.laneA k + p.n + 32)) p.n = V (min (c₀ + k) (p.len - 1)))
    {Q : State → Prop}
    (k : ∀ u, (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → g ≠ .r11 → u.gpr g = u₀.gpr g) →
      u.rd = u₀.rd → u.wr = u₀.wr →
      u.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 (c₀ + 4) →
      u.cf = some (decide (c₀ + 4 < p.len)) →
      (∀ c < p.len, bytesAt u.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
        if c₀ ≤ c ∧ c < c₀ + 4 then V c else bytesAt u₀.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n) →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩, ⟨at' S (Layout.oVar 1 0), 8⟩] u₀.mem u.mem → Q u) :
    WP isa (.block ((List.range 4).flatMap (fun k' => Impl.SlhDsa.X86_64.Verify.chainOf p k' ++
        ([.mov .rdx (.reg .r10)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        Impl.SlhDsa.X86_64.copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
          (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++
      ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Verify.xv 0)), .alu .add .rax (.imm 4), .store (Impl.SlhDsa.X86_64.Verify.xv 0) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.len))] : List Instr))) u₀ Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  rw [List.range_succ, List.range_succ, List.range_succ, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton,
    List.flatMap_singleton, List.flatMap_singleton, List.append_assoc, List.append_assoc, List.append_assoc]
  have hE₀ : EInv p S c₀ u₀ V 0 u₀ := ⟨hbx, fun _ _ _ _ _ _ => rfl, rfl, rfl, hv0, Frame.refl _ _,
    fun c _ => by rw [ite_eq_right (by omega)]⟩
  refine estep hn hlen1 hlen hlB (by decide) hc₀ (by omega) hw hval hE₀ fun u₁ hu₁ => ?_
  refine estep hn hlen1 hlen hlB (by decide) hc₀ (by omega) hw hval hu₁ fun u₂ hu₂ => ?_
  refine estep hn hlen1 hlen hlB (by decide) hc₀ (by omega) hw hval hu₂ fun u₃ hu₃ => ?_
  refine estep hn hlen1 hlen hlB (by decide) hc₀ (by omega) hw hval hu₃ fun u hu => ?_
  -- `c₀ + 4`
  refine wp_movm (a := at' S (Layout.oVar 1 0)) (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hu.bx])
    (by rw [hu.rd, hu.wr, oVar10]; exact in_scr' hw (by omega)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 1 0))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, u₆.other _ (by decide), u₅.other _ (by decide), hu.bx])
    (by rw [u₆.wr, u₅.wr, hu.wr, oVar10]; exact in_scr hw (by omega)) fun s₇ g₇ m₇ r₇ w₇ => ?_
  refine wp_cmpi_cf fun s₈ g₈ m₈ r₈ w₈ _ c₈ => WP.block_nil ?_
  have hrax : s₆.gpr .rax = BitVec.ofNat 64 (c₀ + 4) := by
    rw [u₆.gpr, u₅.gpr, hu.v0, show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 by decide]
    exact (BitVec.ofNat_add c₀ 4).symm
  have hm₈ : s₈.mem = u.mem.writeW (at' S (Layout.oVar 1 0)) (BitVec.ofNat 64 (c₀ + 4)) := by
    rw [m₈, m₇, hrax, u₆.mem, u₅.mem]
  have F₈ : Frame [⟨at' S (Layout.oVar 1 0), 8⟩] u.mem s₈.mem := by
    rw [hm₈]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have eB : Layout.laneB 0 = 3808 := rfl
  refine k s₈ (fun g h1 h2 h3 h4 h5 => by rw [g₈, g₇, u₆.other _ h1, u₅.other _ h1, hu.gpr _ h1 h2 h3 h4 h5])
    (by rw [r₈, r₇, u₆.rd, u₅.rd, hu.rd]) (by rw [w₈, w₇, u₆.wr, u₅.wr, hu.wr])
    (by rw [hm₈]; exact Mem.readW_writeW_self64 _ _ _) ?_ (fun c hc => ?_) ?_
  · rw [c₈, g₇, hrax, sx_ofNat (by omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    have hln : p.len * p.n ≤ 128 * p.n := Nat.mul_le_mul_right _ hlen
    rw [bytesAt_frame F₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar10, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega), hu.ends c hc]
  · refine (hu.frame.sub fun r hr => ?_).trans (F₈.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- A group's lanes after its steps. -/
structure GMid (p : Params) (S sig : Addr) (idx c₀ : Nat) (pkSeed a16 : List Byte) (s : State) (t₀ stack : Nat)
    (t : State) : Prop where
  gpr : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  v0 : t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀
  val : ∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
    runTo p pkSeed (adrsOf a16 0 idx (min (c₀ + k) (p.len - 1)) 0)
      (bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n)
      (s.mem (at' S (Layout.oDigits + min (c₀ + k) (p.len - 1)))).toNat t₀ 15
  frame : Frame (chFrame p S (s.gpr .rsp) stack) s.mem t.mem

/-- A group of four chains (`chainGroup`), from `c₀` (variable 0): each
chain's end, `chain(sig_c, d_c, 15 - d_c)`, at its place in lane 0 of `B`'s
message; then `c₀ + 4` in variable 0, CF set while below `len`. -/
theorem chainGroup_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    (hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {idx c₀ : Nat} {pkSeed a16 : List Byte} (hc₀ : c₀ < p.len) (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd) (hsfit : sig.toNat + sL ≤ 2 ^ 64)
    (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (hsb : Region.Disjoint ⟨sig, sL⟩ (below (s.gpr .rsp) stack))
    (hD : ∀ c < p.len, (s.mem (at' S (Layout.oDigits + c))).toNat ≤ 15)
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr →
      t'.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 (c₀ + 4) →
      t'.cf = some (decide (c₀ + 4 < p.len)) →
      (∀ c < p.len, bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
        if c₀ ≤ c ∧ c < c₀ + 4 then
          chain p (bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n) (s.mem (at' S (Layout.oDigits + c))).toNat
            (15 - (s.mem (at' S (Layout.oDigits + c))).toNat) pkSeed (adrsOf a16 0 idx c 0)
        else bytesAt s.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n) →
      Frame (chFrame p S (s.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩]) s.mem t'.mem →
      Q t') :
    WP isa (Impl.SlhDsa.X86_64.Verify.chainGroup p f) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have eB : Layout.laneB 0 = 3808 := rfl
  have hc₀' : c₀ + 4 < 2 ^ 31 := by omega
  unfold Impl.SlhDsa.X86_64.Verify.chainGroup
  refine WP.seq (chainLanes_ok hn hlen1 hlen hc₀' hidx hbx h12 h13 hv0 hw hsr hsfit hss hsL fun u hu => ?_)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = dmin p s.mem S c₀ 4 := ⟨_, rfl⟩
  have ht₀15 : t₀ ≤ 15 := by rw [ht₀]; exact dmin_le _ _ _ _ _
  have hv2 := hu.v2
  rw [← ht₀] at hv2
  -- variable 1 ← the least digit; CF if below 15
  refine WP.seq (wp_movm (a := at' S (Layout.oVar 1 2))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, hu.bx])
    (by rw [hu.rd, hu.wr, oVar12]; exact in_scr' hw (by omega)) fun s₁ u₁ => ?_)
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 1 1))
    (by rw [Impl.SlhDsa.X86_64.Verify.xv, Proof.Sha3.X86_64.ea_at, u₁.other _ (by decide), hu.bx])
    (by rw [u₁.wr, hu.wr, oVar11]; exact in_scr hw (by omega)) fun s₂ g₂ m₂ r₂ w₂ => ?_
  refine wp_cmpi_cf fun s₃ g₃ m₃ r₃ w₃ _ c₃ => WP.block_nil ?_
  have hrax : s₂.gpr .rax = BitVec.ofNat 64 t₀ := by rw [g₂, u₁.gpr, hv2]
  rw [hrax, show BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 15 by decide] at c₃
  simp only [BitVec.toNat_ofNat] at c₃
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at c₃
  have hm₃ : s₃.mem = u.mem.writeW (at' S (Layout.oVar 1 1)) (BitVec.ofNat 64 t₀) := by
    rw [m₃, m₂, u₁.gpr, hv2, u₁.mem]
  have F₃ : Frame [⟨at' S (Layout.oVar 1 1), 8⟩] u.mem s₃.mem := by
    rw [hm₃]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have D3 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 2584 ∨ 2592 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.oVar 1 1), 8⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [oVar11]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have Fs₃ : Frame (chFrame p S (s.gpr .rsp) stack) s.mem s₃.mem := by
    refine (hu.frame.sub fun r hr => ?_).trans (F₃.sub fun r hr => ?_)
    · simp only [initR, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
          Offset.sub S (by omega) (by rw [eA]; simp only [Layout.strideA]; omega)⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
          Offset.sub S (by simp only [oVar12, oVar10]; omega) (by simp only [oVar12, oVar10]; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
        Offset.sub S (by simp only [oVar11, oVar10]; omega) (by simp only [oVar11, oVar10]; omega)⟩
  -- what `chFrame` leaves
  have hdig : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack) s.mem m → ∀ c < 128,
      m (at' S (Layout.oDigits + c)) = s.mem (at' S (Layout.oDigits + c)) := fun hf c hc =>
    frame_at hf (chFrame_disj hn32 hstk (l := 1) (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega))
  have hsig : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack) s.mem m → ∀ c < p.len,
      bytesAt m (sig + BitVec.ofNat 64 (c * p.n)) p.n = bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n :=
    fun hf c hc => by
      have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
      have hsub : Region.Sub ⟨sig + BitVec.ofNat 64 (c * p.n), p.n⟩ ⟨sig, sL⟩ := Offset.sub_base sig (by omega)
      exact bytesAt_frame hf (chFrame_disj' hn32 (hss.sub_left hsub) (hsb.sub_left hsub)) (by omega)
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp := by
    rw [g₃, g₂, u₁.other _ (by decide), hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hcs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃, g₂, u₁.other _ h.1, hu.gpr _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2]
  have hv0₃ : s₃.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀ := by
    rw [F₃.readW (Region.contains_self _ _) (D3 (by rw [oVar10]; omega) (by rw [oVar10]; omega)) (by decide), hu.v0]
  have hval₃ : ∀ k < 4, bytesAt s₃.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      bytesAt s.mem (sig + BitVec.ofNat 64 (min (c₀ + k) (p.len - 1) * p.n)) p.n := fun k hk => by
    rw [bytesAt_frame F₃ (D3 (by rw [eA]; omega) (by rw [eA]; omega)) (by omega)]; exact (hu.done k hk).value
  have hfld₃ : ∀ k < 4, bytesAt s₃.mem (at' S (Layout.laneA k + p.n + 16)) 12 =
      toByte 0 4 ++ toByte idx 4 ++ toByte (min (c₀ + k) (p.len - 1)) 4 := fun k hk => by
    rw [bytesAt_frame F₃ (D3 (by rw [eA]; omega) (by rw [eA]; omega)) (by omega)]; exact (hu.done k hk).fields
  -- the steps, if any
  refine WP.seq (WP.mono (Q := GMid p S sig idx c₀ pkSeed a16 s t₀ stack) ?_ fun t ht => ?_)
  · refine WP.ite (decide (t₀ < 15)) c₃ (fun h => ?_) (fun h => WP.block_nil ?_)
    · have h' : t₀ < 15 := of_decide_eq_true h
      have henv₃ := Env.of_frame hn32 henv (Fs₃.sub (chFrame_sub p S _ stack)) hstk
      refine stepLoop_ok T ht hn hfam hlen1 hlen hst hs63 hc₀' h' (by rw [hcs₃ _ (by decide), hbx])
        (by rw [hcs₃ _ (by decide), h13]) hv0₃
        (by rw [hm₃]; exact Mem.readW_writeW_self64 _ _ _) (by rw [w₃, w₂, u₁.wr, hu.wr]; exact hw) hS
        (by rw [hsp₃]; exact hstk) henv₃ hfld₃ (by rw [r₃, r₂, u₁.rd, hu.rd]; exact hsr) hsfit hss hsL
        (by rw [hsp₃]; exact hsb) (fun k hk => by rw [hval₃ k hk, hsig Fs₃ _ (by omega)])
        fun t' g' r' w' v0' _ l' F' => ⟨fun r hr => by rw [g' r hr, hcs₃ r hr], by rw [r', r₃, r₂, u₁.rd, hu.rd],
          by rw [w', w₃, w₂, u₁.wr, hu.wr], v0', fun k hk => by
            rw [l' k hk, hsig Fs₃ _ (by omega), hdig Fs₃ _ (by omega)], Fs₃.trans (by rw [hsp₃] at F'; exact F')⟩
    · have h' : t₀ = 15 := by have := of_decide_eq_false h; omega
      exact ⟨hcs₃, by rw [r₃, r₂, u₁.rd, hu.rd], by rw [w₃, w₂, u₁.wr, hu.wr], hv0₃, fun k hk => by
        rw [hval₃ k hk, h']; simp only [runTo, Nat.sub_self, List.range_zero, List.foldl_nil], Fs₃⟩
  -- the ends
  have hbt : t.gpr .rbx = S := by rw [ht.gpr _ (by decide), hbx]
  refine ends_ok hn hlen1 hlen hlB (V := fun c => runTo p pkSeed (adrsOf a16 0 idx c 0)
      (bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n) (s.mem (at' S (Layout.oDigits + c))).toNat t₀ 15)
    hc₀ hbt ht.v0 (by rw [ht.wr]; exact hw) ht.val fun u' g' r' w' v0' c' e' F' => ?_
  refine k u' (fun r hr => ?_) (by rw [r', ht.rd]) (by rw [w', ht.wr]) v0' c' (fun c hc => ?_) ?_
  · have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g' _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2, ht.gpr r hr]
  · have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    have hln : p.len * p.n ≤ 128 * p.n := Nat.mul_le_mul_right _ hlen
    rw [e' c hc, bytesAt_frame ht.frame (chFrame_disj hn32 hstk (by rw [eB]; omega) (by rw [eB]; omega)) (by omega)]
    by_cases hg : c₀ ≤ c ∧ c < c₀ + 4
    · rw [ite_eq_left hg, ite_eq_left hg]
      have hd := dmin_le_digit p s.mem S c₀ 4 (c - c₀) (by omega)
      rw [show min (c₀ + (c - c₀)) (p.len - 1) = c by omega, ← ht₀] at hd
      exact chain_restore p pkSeed _ _ hd (hD c hc)
    · rw [ite_eq_right hg, ite_eq_right hg]
  · refine ht.frame.mono (fun r hr => List.mem_append_left _ hr) |>.trans (F'.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by simp only [oVar10, oVar10]; omega) (by simp only [oVar10, oVar10]; omega)⟩

/-- The groups of chains, from chain 0 (variable 0): every chain's end
`chain(sig_c, d_c, 15 - d_c)` at its place in lane 0 of `B`'s message. -/
theorem groupLoop_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hlen1 : 1 ≤ p.len) (hlen : p.len ≤ 128)
    (hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {idx : Nat} {pkSeed a16 : List Byte} (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 0)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    {sL : Nat} (hsr : (⟨sig, sL⟩ : Region) ∈ s.rd) (hsfit : sig.toNat + sL ≤ 2 ^ 64)
    (hss : Region.Disjoint ⟨sig, sL⟩ ⟨S, 2 ^ 16⟩) (hsL : p.len * p.n ≤ sL)
    (hsb : Region.Disjoint ⟨sig, sL⟩ (below (s.gpr .rsp) stack))
    (hD : ∀ c < p.len, (s.mem (at' S (Layout.oDigits + c))).toNat ≤ 15)
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr →
      (∀ c < p.len, bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
        chain p (bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n) (s.mem (at' S (Layout.oDigits + c))).toNat
          (15 - (s.mem (at' S (Layout.oDigits + c))).toNat) pkSeed (adrsOf a16 0 idx c 0)) →
      Frame (chFrame p S (s.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩]) s.mem t'.mem →
      Q t') :
    WP isa (.loop (Impl.SlhDsa.X86_64.Verify.chainGroup p f) .b) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eB : Layout.laneB 0 = 3808 := rfl
  -- what the frame leaves: the digits, the signature, `Env`
  have hF : ∀ r ∈ chFrame p S (s.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩],
      ∃ r' ∈ changes p S ++ [below (s.gpr .rsp) stack], Region.Sub r r' := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact chFrame_sub p S _ stack r hr
    · rw [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
        Offset.sub S (e := Layout.laneB 0 + p.n + 16) (k := Layout.strideB - p.n - 16) (by omega) (by omega)⟩
  have hdig : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩])
      s.mem m → ∀ c < 128, m (at' S (Layout.oDigits + c)) = s.mem (at' S (Layout.oDigits + c)) := fun hf c hc =>
    frame_at hf fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact chFrame_disj hn32 hstk (l := 1) (by rw [oDigits_eq]; omega) (by rw [oDigits_eq]; omega) r hr
      · rw [List.mem_singleton] at hr; subst hr
        have hln : p.len * p.n ≤ 128 * 32 := Nat.mul_le_mul hlen hn32
        rw [oDigits_eq, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hsig : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩])
      s.mem m → ∀ c < p.len,
      bytesAt m (sig + BitVec.ofNat 64 (c * p.n)) p.n = bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n :=
    fun hf c hc => by
      have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
      have hsub : Region.Sub ⟨sig + BitVec.ofNat 64 (c * p.n), p.n⟩ ⟨sig, sL⟩ := Offset.sub_base sig (by omega)
      exact bytesAt_frame hf (fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact chFrame_disj' hn32 (hss.sub_left hsub) (hsb.sub_left hsub) r hr
        · rw [List.mem_singleton] at hr; subst hr
          exact (hss.sub_left hsub).sub_right (Offset.sub_base S (by
            have hln : p.len * p.n ≤ 128 * 32 := Nat.mul_le_mul hlen hn32
            rw [eB]; omega))) (by omega)
  let Inv : Nat → State → Prop := fun m t => ∃ c₀, m = p.len - c₀ ∧ c₀ < p.len ∧
    (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.mem.readW (at' S (Layout.oVar 1 0)) 64 = BitVec.ofNat 64 c₀ ∧
    (∀ c < p.len, c < c₀ → bytesAt t.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
      chain p (bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n) (s.mem (at' S (Layout.oDigits + c))).toNat
        (15 - (s.mem (at' S (Layout.oDigits + c))).toNat) pkSeed (adrsOf a16 0 idx c 0)) ∧
    Frame (chFrame p S (s.gpr .rsp) stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.len * p.n⟩]) s.mem t.mem
  have hbxcs : Reg.rbx ∈ calleeSaved := by decide
  have h12cs : Reg.r12 ∈ calleeSaved := by decide
  have h13cs : Reg.r13 ∈ calleeSaved := by decide
  have hspcs : Reg.rsp ∈ calleeSaved := by decide
  refine WP.loop (M := isa) Inv (fun m t ⟨c₀, hm, hc₀, gt, rt, wt, v0t, et, Ft⟩ => ?_) (p.len - 0) s
    ⟨0, rfl, by omega, fun _ _ => rfl, rfl, rfl, hv0, fun _ _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  have hsp : t.gpr .rsp = s.gpr .rsp := gt _ hspcs
  have henvt := Env.of_frame hn32 henv (Ft.sub hF) hstk
  refine chainGroup_ok T ht hn hfam hlen1 hlen hlB hst hs63 hc₀ hidx (by rw [gt _ hbxcs, hbx])
    (by rw [gt _ h12cs, h12]) (by rw [gt _ h13cs, h13]) v0t (by rw [wt]; exact hw) hS (by rw [hsp]; exact hstk) henvt
    (by rw [rt]; exact hsr) hsfit hss hsL (by rw [hsp]; exact hsb) (fun c hc => by rw [hdig Ft c (by omega)]; exact hD c hc)
    fun t' g' r' w' v0' c' e' F' => ?_
  rw [hsp] at F'
  have Ft' := Ft.trans F'
  have he' : ∀ c < p.len, c < c₀ + 4 → bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
      chain p (bytesAt s.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n) (s.mem (at' S (Layout.oDigits + c))).toNat
        (15 - (s.mem (at' S (Layout.oDigits + c))).toNat) pkSeed (adrsOf a16 0 idx c 0) := fun c hc hc4 => by
    rw [e' c hc]
    by_cases hg : c₀ ≤ c ∧ c < c₀ + 4
    · rw [ite_eq_left hg, hsig Ft c hc, hdig Ft c (by omega)]
    · rw [ite_eq_right hg]; exact et c hc (by omega)
  by_cases hlast : c₀ + 4 < p.len
  · refine Or.inr ⟨by show t'.cf = some true; rw [c', decide_eq_true hlast], p.len - (c₀ + 4), by omega, c₀ + 4, rfl,
      hlast, fun r hr => by rw [g' r hr, gt r hr], by rw [r', rt], by rw [w', wt], v0', fun c hc hc4 => he' c hc hc4,
      Ft'⟩
  · refine Or.inl ⟨by show t'.cf = some false; rw [c', decide_eq_false hlast], ?_⟩
    exact k t' (fun r hr => by rw [g' r hr, gt r hr]) (by rw [r', rt]) (by rw [w', wt])
      (fun c hc => he' c hc (by omega)) Ft'

end VG.Proof.SlhDsa.X86_64
