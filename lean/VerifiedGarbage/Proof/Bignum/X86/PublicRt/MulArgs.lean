module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The arguments of a multiplication in public RSA at a run-time width

`mulArgs o a b` stores the nine arguments of `vg_rsa_mont_mul` into the
frame of 36 bytes at `esp` (`mulArgs_ok`): word `i` is `mulArg … i`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86

/-- Argument `i` of the call for the numbers `o`, `a` and `b`, from `edi` and `ws_len`. -/
def mulArg (len o a b : Nat) (edi wsLen : BitVec 32) : Nat → BitVec 32
  | 0 => edi
  | 1 => wsLen
  | 2 => BitVec.ofNat 32 (Spec.Rsa.modulusWords len)
  | 3 => BitVec.ofNat 32 numOff
  | 4 => BitVec.ofNat 32 invOff
  | 5 => BitVec.ofNat 32 (numAt len 5)
  | 6 => BitVec.ofNat 32 (numAt len o)
  | 7 => BitVec.ofNat 32 (numAt len a)
  | _ => BitVec.ofNat 32 (numAt len b)

/-- `offEax j`: `eax = 256 + j B`, from `edx = B`. -/
theorem offEax_ok {s : State} {is : List Instr} {Q : State → Prop} {len j : Nat}
    (hedx : s.gpr .edx = BitVec.ofNat 32 (wb len)) (hl : len ≤ 1024) (hj : j ≤ 8)
    (kk : ∀ u, Keeps [.eax] s u → u.mem = s.mem → u.gpr .eax = BitVec.ofNat 32 (numAt len j) →
      WP isa (.block is) u Q) :
    WP isa (.block (offEax j ++ is)) s Q := by
  have hw := wb_le hl
  simp only [offEax, List.cons_append]
  refine wp_movS rfl fun s₁ u₁ _ => adds_ok (r := .eax) (t := .edx) (by decide) j fun u K m e => ?_
  refine kk u (u₁.keeps.trans K) (by rw [m, u₁.mem]) ?_
  rw [e, u₁.gpr, u₁.other _ (by decide), hedx]
  apply BitVec.eq_of_toNat_eq
  have : j * wb len ≤ 8 * 1024 := Nat.mul_le_mul hj hw
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, numAt, numOff]
  rw [Nat.mod_eq_of_lt (a := wb len) (by omega), Nat.mod_eq_of_lt (a := j * wb len) (by omega)]

/-- A store into the frame at `esp`. -/
theorem frame_store {t : State} {P : Addr} (hP : (t.gpr .esp).setWidth 64 = P) (hesp : (t.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (hfr : (⟨P, 36⟩ : Region) ∈ t.wr) {k : Nat} (hk : k + 4 ≤ 36) :
    t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 := by
  refine ⟨?_, ⟨_, hfr, Offset.contains_base _ hk (by omega)⟩⟩
  rw [at_, ea_mk, addr_eq (by omega), hP]

/-- A word of the frame, after a store to another. -/
theorem frame_other (m : Mem) (P : Addr) (v : BitVec 32) {k j : Nat} (h : j + 4 ≤ k ∨ k + 4 ≤ j)
    (hk : k + 4 ≤ 36) (hj : j + 4 ≤ 36) :
    (m.writeW (P + BitVec.ofNat 64 k) v).readW (P + BitVec.ofNat 64 j) 32 = m.readW (P + BitVec.ofNat 64 j) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega) (by omega)) (by decide)

theorem mulArgs_ok {f : State} {len o a b : Nat} {wsLen : BitVec 32}
    (hr3 : readSrc f (.mem (argAt 9 1)) = some (BitVec.ofNat 32 len))
    (hr9 : readSrc f (.mem (argAt 9 9)) = some wsLen)
    (hl : len ≤ 1024) (ho : o ≤ 8) (ha : a ≤ 8) (hb : b ≤ 8)
    (hesp : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (hfr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (mulArgs o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        mulArg len o a b (f.gpr .edi) wsLen i := by
  have hw := wb_le hl
  generalize hP : (f.gpr .esp).setWidth 64 = P at hfr ⊢
  simp only [mulArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine widthB_ok hr3 hl fun s₁ K₁ m₁ e₁ => ?_
  -- A state reached by registers but `esp`: the same frame.
  have fr : ∀ t : State, t.gpr .esp = f.gpr .esp → t.wr = f.wr → ∀ k, k + 4 ≤ 36 →
      t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 :=
    fun t he hw' k hk => frame_store (by rw [he, hP]) (by rw [he]; exact hesp) (by rw [hw']; exact hfr) hk
  have sp₁ : s₁.gpr .esp = f.gpr .esp := K₁.1 _ (by decide)
  have edi₁ : s₁.gpr .edi = f.gpr .edi := K₁.1 _ (by decide)
  have hr9₁ : readSrc s₁ (.mem (argAt 9 9)) = some wsLen := by
    rw [← hr9]; simp only [readSrc, State.load32, State.ea, argAt, at_, sp₁, m₁, K₁.2.1, K₁.2.2]; rfl
  refine wp_movS hr9₁ fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.eax, .edx] f s₂ := (K₁.mono (by decide)).trans (u₂.keeps.mono (by decide))
  obtain ⟨a₄, w₄⟩ := fr s₂ (K₂.1 _ (by decide)) K₂.2.2 4 (by decide)
  refine wp_storeS a₄ w₄ fun s₃ m₃ => ?_
  obtain ⟨a₀, w₀⟩ := fr s₃ (by rw [m₃.gpr]; exact K₂.1 _ (by decide)) (by rw [m₃.wr]; exact K₂.2.2) 0 (by decide)
  refine wp_storeS a₀ w₀ fun s₄ m₄ => ?_
  have K₄ : Keeps [.eax, .edx] f s₄ := (K₂.trans (m₃.keeps _)).trans (m₄.keeps _)
  refine wp_movS rfl fun s₅ u₅ _ => wp_shr (by decide) fun s₆ u₆ => ?_
  have K₆ : Keeps [.eax, .edx] f s₆ := (K₄.trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  obtain ⟨a₈, w₈⟩ := fr s₆ (K₆.1 _ (by decide)) K₆.2.2 8 (by decide)
  refine wp_storeS a₈ w₈ fun s₇ m₇ => wp_movS rfl fun s₈ u₈ _ => ?_
  have K₈ : Keeps [.eax, .edx] f s₈ := (K₆.trans (m₇.keeps _)).trans (u₈.keeps.mono (by decide))
  obtain ⟨a₁₂, w₁₂⟩ := fr s₈ (K₈.1 _ (by decide)) K₈.2.2 12 (by decide)
  refine wp_storeS a₁₂ w₁₂ fun s₉ m₉ => wp_movS rfl fun s₁₀ u₁₀ _ => ?_
  have K₁₀ : Keeps [.eax, .edx] f s₁₀ := (K₈.trans (m₉.keeps _)).trans (u₁₀.keeps.mono (by decide))
  obtain ⟨a₁₆, w₁₆⟩ := fr s₁₀ (K₁₀.1 _ (by decide)) K₁₀.2.2 16 (by decide)
  refine wp_storeS a₁₆ w₁₆ fun s₁₁ m₁₁ => ?_
  have K₁₁ : Keeps [.eax, .edx] f s₁₁ := K₁₀.trans (m₁₁.keeps _)
  -- `edx` holds `B` from `widthB` on.
  have edx : ∀ t : State, Keeps [.eax] s₁ t → t.gpr .edx = BitVec.ofNat 32 (wb len) :=
    fun t K => by rw [K.1 _ (by decide), e₁]
  have edx₁₁ : s₁₁.gpr .edx = BitVec.ofNat 32 (wb len) := edx s₁₁ (by
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [m₁₁.gpr, u₁₀.other _ (by simpa using hr), m₉.gpr, u₈.other _ (by simpa using hr), m₇.gpr,
        u₆.other _ (by simpa using hr), u₅.other _ (by simpa using hr), m₄.gpr, m₃.gpr,
        u₂.other _ (by simpa using hr)]
    · rw [m₁₁.rd, u₁₀.rd, m₉.rd, u₈.rd, m₇.rd, u₆.rd, u₅.rd, m₄.rd, m₃.rd, u₂.rd]
    · rw [m₁₁.wr, u₁₀.wr, m₉.wr, u₈.wr, m₇.wr, u₆.wr, u₅.wr, m₄.wr, m₃.wr, u₂.wr])
  refine offEax_ok (j := 5) edx₁₁ hl (by decide) fun s₁₂ K₁₂ m₁₂ e₁₂ => ?_
  have K₁₂' : Keeps [.eax, .edx] f s₁₂ := K₁₁.trans (K₁₂.mono (by decide))
  obtain ⟨a₂₀, w₂₀⟩ := fr s₁₂ (K₁₂'.1 _ (by decide)) K₁₂'.2.2 20 (by decide)
  refine wp_storeS a₂₀ w₂₀ fun s₁₃ m₁₃ => ?_
  have edx₁₃ : s₁₃.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₁₃.gpr, K₁₂.1 _ (by decide), edx₁₁]
  refine offEax_ok (j := o) edx₁₃ hl ho fun s₁₄ K₁₄ m₁₄ e₁₄ => ?_
  have K₁₄' : Keeps [.eax, .edx] f s₁₄ := (K₁₂'.trans (m₁₃.keeps _)).trans (K₁₄.mono (by decide))
  obtain ⟨a₂₄, w₂₄⟩ := fr s₁₄ (K₁₄'.1 _ (by decide)) K₁₄'.2.2 24 (by decide)
  refine wp_storeS a₂₄ w₂₄ fun s₁₅ m₁₅ => ?_
  have edx₁₅ : s₁₅.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₁₅.gpr, K₁₄.1 _ (by decide), edx₁₃]
  refine offEax_ok (j := a) edx₁₅ hl ha fun s₁₆ K₁₆ m₁₆ e₁₆ => ?_
  have K₁₆' : Keeps [.eax, .edx] f s₁₆ := (K₁₄'.trans (m₁₅.keeps _)).trans (K₁₆.mono (by decide))
  obtain ⟨a₂₈, w₂₈⟩ := fr s₁₆ (K₁₆'.1 _ (by decide)) K₁₆'.2.2 28 (by decide)
  refine wp_storeS a₂₈ w₂₈ fun s₁₇ m₁₇ => ?_
  have edx₁₇ : s₁₇.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₁₇.gpr, K₁₆.1 _ (by decide), edx₁₅]
  refine offEax_ok (j := b) edx₁₇ hl hb fun s₁₈ K₁₈ m₁₈ e₁₈ => ?_
  have K₁₈' : Keeps [.eax, .edx] f s₁₈ := (K₁₆'.trans (m₁₇.keeps _)).trans (K₁₈.mono (by decide))
  obtain ⟨a₃₂, w₃₂⟩ := fr s₁₈ (K₁₈'.1 _ (by decide)) K₁₈'.2.2 32 (by decide)
  refine wp_storeS a₃₂ w₃₂ fun g mg => WP.block_nil ?_
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₄.gpr, m₃.gpr, u₂.other _ (by decide), e₁]
  have eW : s₆.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) := by
    rw [u₆.gpr, u₅.gpr, edx₄]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, wb]
    have : 8 * Spec.Rsa.modulusWords len ≤ 1024 := hw
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by simp only [Spec.Rsa.modulusWords]; omega)]
    omega
  have mem : g.mem = ((((((((f.mem.writeW (P + BitVec.ofNat 64 4) wsLen).writeW (P + BitVec.ofNat 64 0)
      (f.gpr .edi)).writeW (P + BitVec.ofNat 64 8) (BitVec.ofNat 32 (Spec.Rsa.modulusWords len))).writeW
      (P + BitVec.ofNat 64 12) (BitVec.ofNat 32 numOff)).writeW (P + BitVec.ofNat 64 16)
      (BitVec.ofNat 32 invOff)).writeW (P + BitVec.ofNat 64 20) (BitVec.ofNat 32 (numAt len 5))).writeW
      (P + BitVec.ofNat 64 24) (BitVec.ofNat 32 (numAt len o))).writeW (P + BitVec.ofNat 64 28)
      (BitVec.ofNat 32 (numAt len a))).writeW (P + BitVec.ofNat 64 32) (BitVec.ofNat 32 (numAt len b)) := by
    rw [mg.mem, m₁₈, m₁₇.mem, m₁₆, m₁₅.mem, m₁₄, m₁₃.mem, m₁₂, m₁₁.mem, u₁₀.mem, m₉.mem, u₈.mem, m₇.mem,
      u₆.mem, u₅.mem, m₄.mem, m₃.mem, u₂.mem, m₁, e₁₈, e₁₆, e₁₄, e₁₂, u₁₀.gpr, u₈.gpr, eW, m₃.gpr,
      u₂.gpr, u₂.other .edi (by decide), edi₁]
  refine ⟨K₁₈'.trans (mg.keeps _), ?_, ?_⟩
  · have fw : ∀ {m : Mem} (k : Nat) (v : BitVec 32), k + 4 ≤ 36 → Frame [⟨P, 36⟩] f.mem m →
        Frame [⟨P, 36⟩] f.mem (m.writeW (P + BitVec.ofNat 64 k) v) := fun k v hk F =>
      F.writeW (List.mem_singleton_self _) v (Offset.contains_base _ hk (by omega))
    rw [mem]
    exact fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) (Frame.refl _ _)
  · intro i hi
    rw [mem]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first
      | omega
      | simp (disch := decide) only [frame_other, Mem.readW_writeW_self32, mulArg, Nat.mul_zero, Nat.reduceMul,
          Nat.reduceAdd, Nat.zero_add]

end VG.Proof.Bignum.X86.PublicRt
