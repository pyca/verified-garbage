module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Decode
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 on PPC64LE: the two sides of the verification equation

With `pk`, the signature and the challenge in `r29`–`r31` (`VCtx`), `A` and
`R` decoded into the tables at 7776 and 7904, and the static of `-[1]B …
-[15]B` (`BStat`): the comparison of the points in slots 0–3 and 4–7
(`pointEqual_ok`), the challenge's top half (`challengeHigh_ok`), and what
the windows' proof gives (`RhsOk`), the result in `r17`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

/-- **The comparison** of the points in slots 0–3 and 4–7, into `r17`. -/
theorem pointEqual_ok {s : State} (hc : Ctx8 b s) :
    WP isa Impl.Ed25519.PPC64LE.pointEqual s fun t => DKeep b s t ∧
      t.gpr .r17 = if Spec.Ed25519.pointEqual (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 4 5 6 7)
        then 1 else 0 := by
  unfold Impl.Ed25519.PPC64LE.pointEqual
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx) fun s1 ⟨k1, e1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (WP.mono (fieldEqual_ok hc1.ctx 8 9) fun s2 ⟨k2, e2, h2⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  have x8 : env s1.mem b 8 = env s.mem b 0 * env s.mem b 6 := by rw [e1]; rfl
  have x9 : env s1.mem b 9 = env s.mem b 4 * env s.mem b 2 := by rw [e1]; rfl
  have x10 : env s2.mem b 10 = env s.mem b 1 * env s.mem b 6 := by rw [e2, e1]; rfl
  have x11 : env s2.mem b 11 = env s.mem b 5 * env s.mem b 2 := by rw [e2, e1]; rfl
  rw [x8, x9] at h2
  have hk2 : DKeep b s s2 := DKeep.of_keep (k1.trans k2)
  unfold Spec.Ed25519.pointEqual
  simp only [point]
  refine WP.ite (s2.gpr .r5 == 0) (eval_zero s2 .r5) (fun h => ?_) (fun h => ?_)
  · have ha := h2.mp (beq_iff_eq.mp h)
    refine WP.seq (WP.mono (fieldEqual_ok hc2.ctx 10 11) fun s3 ⟨k3, _, h3⟩ => ?_)
    rw [x10, x11] at h3
    have hk3 : DKeep b s s3 := hk2.trans (DKeep.of_keep k3)
    refine WP.ite (s3.gpr .r5 == 0) (eval_zero s3 .r5) (fun h' => ?_) (fun h' => ?_)
    · refine wp_li (by decide) fun t u => WP.block_nil
        ⟨hk3.trans ⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, ?_⟩
      rw [u.gpr]
      simp [ha, h3.mp (beq_iff_eq.mp h')]
    · have hb : ¬ env s.mem b 1 * env s.mem b 6 = env s.mem b 5 * env s.mem b 2 :=
        fun he => absurd (beq_iff_eq.mpr (h3.mpr he)) (by simpa using h')
      refine WP.mono (recoverInvalid_ok s3) fun t ⟨kt, _, dt⟩ => ⟨hk3.trans kt, ?_⟩
      rw [show t.gpr .r17 = 0 from dt]
      simp [ha, hb]
  · have hb : ¬ env s.mem b 0 * env s.mem b 6 = env s.mem b 4 * env s.mem b 2 :=
      fun he => absurd (beq_iff_eq.mpr (h2.mpr he)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s2) fun t ⟨kt, _, dt⟩ => ⟨hk2.trans kt, ?_⟩
    rw [show t.gpr .r17 = 0 from dt]
    simp [hb]

end

/-- The verification's inputs: `pk`, the signature and the challenge, readable at `r29`–`r31`,
outside the working space at `r6`. -/
structure VCtx (b pk sig ch : Addr) (s : State) : Prop where
  ctx : Ctx8 b s
  r29 : s.gpr .r29 = pk
  r30 : s.gpr .r30 = sig
  r31 : s.gpr .r31 = ch
  pkR : (⟨pk, 32⟩ : Region) ∈ s.rd
  sigR : (⟨sig, 64⟩ : Region) ∈ s.rd
  chR : (⟨ch, 64⟩ : Region) ∈ s.rd
  pkD : (⟨pk, 32⟩ : Region).Disjoint ⟨b, 8192⟩
  sigD : (⟨sig, 64⟩ : Region).Disjoint ⟨b, 8192⟩
  chD : (⟨ch, 64⟩ : Region).Disjoint ⟨b, 8192⟩

section
variable {b pk sig ch : Addr}

theorem VCtx.of_rest {s t : State} {R : List Reg} (h : VCtx b pk sig ch s) (hr : Rest R s t)
    (hw : ∀ r ∈ [Reg.r6, .r29, .r30, .r31], r ∉ R) : VCtx b pk sig ch t where
  ctx := h.ctx.of_rest hr (hw _ (by simp))
  r29 := by rw [hr.gpr _ (hw _ (by simp)), h.r29]
  r30 := by rw [hr.gpr _ (hw _ (by simp)), h.r30]
  r31 := by rw [hr.gpr _ (hw _ (by simp)), h.r31]
  pkR := by rw [hr.rd]; exact h.pkR
  sigR := by rw [hr.rd]; exact h.sigR
  chR := by rw [hr.rd]; exact h.chR
  pkD := h.pkD
  sigD := h.sigD
  chD := h.chD

/-- Bytes outside the working space, through a frame within it. -/
theorem bytesAt_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : n ≤ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
  intro i hi
  exact bytes_ws hf hs hd hn (List.mem_range.mp hi)

theorem table_sub {o : Nat} (ho : o + 128 ≤ 8192) : Region.Sub ⟨b + BitVec.ofNat 64 o, 128⟩ ⟨b, 8192⟩ :=
  Offset.sub_base b ho

/-- What `[S] P` writes, with a table entry. -/
abbrev sideW (b : Addr) (o : Nat) : List Region := ⟨b + BitVec.ofNat 64 o, 128⟩ :: mulW b

theorem sideW_sub {o : Nat} (ho : o + 128 ≤ 8192) : ∀ r ∈ sideW b o, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact table_sub ho
  · exact mulW_sub r hr

/-- The registers `[S] P` writes. -/
abbrev sideR : List Reg := .r19 :: .r7 :: batchR

/-- A list of zero bytes is the integer 0. -/
theorem decodeLE_zeros : ∀ (l : List (BitVec 8)), (∀ x ∈ l, x = 0) → decodeLE l = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [Proof.Ed25519.decodeLE_cons, h x List.mem_cons_self,
      decodeLE_zeros l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- A challenge whose top 32 bytes are zero is its low 32 bytes. -/
theorem decodeLE_low (m : Mem) (p : Addr) (h : ∀ i < 32, m (p + BitVec.ofNat 64 (32 + i)) = 0) :
    decodeLE (bytesAt m p 64) = decodeLE (bytesAt m p 32) := by
  have hs : bytesAt m p (32 + 32) = bytesAt m p 32 ++ bytesAt m (p + BitVec.ofNat 64 32) 32 :=
    Proof.X25519.bytesAt_add m p 32 32
  rw [show 64 = 32 + 32 from rfl, hs, Proof.Ed25519.decodeLE_append,
    decodeLE_zeros (bytesAt m (p + BitVec.ofNat 64 32) 32) ?_, Nat.mul_zero, Nat.add_zero]
  intro x hx
  simp only [bytesAt, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h i hi

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at h'
    have := Nat.or_eq_zero_iff.mp h'
    exact ⟨BitVec.eq_of_toNat_eq this.1, BitVec.eq_of_toNat_eq this.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The first `n` bytes of the challenge's top half, or-ed into `r8`. -/
theorem challengeOr_ok {ch : Addr} :
    ∀ n ≤ 32, ∀ s : State, s.gpr .r31 = ch →
      (∀ i < 32, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 (32 + i)) 1) →
      WP isa (.block ((List.range n).flatMap fun i =>
          [.lbz .r9 .r31 (32 + i), .logic .or .r8 .r8 .r9])) s fun t =>
        Rest [.r8, .r9] s t ∧ t.mem = s.mem ∧
        (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ ∀ i < n, s.mem (ch + BitVec.ofNat 64 (32 + i)) = 0)
  | 0, _, s, _, _ => WP.block_nil ⟨Rest.refl _ _, rfl, by simp⟩
  | n + 1, hn, s, h31, hin => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (challengeOr_ok n (by omega) s h31 hin) fun s1 ⟨r1, m1, e1⟩ => ?_
    refine wp_lbz (a := ch + BitVec.ofNat 64 (32 + n)) (by decide) (by omega)
      (by rw [r1.gpr _ (by decide), h31]) (by rw [r1.rd, r1.wr]; exact hin n (by omega)) fun s2 u2 => ?_
    refine wp_or fun s3 u3 => WP.block_nil ⟨r1.trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, m1], ?_⟩
    rw [u3.gpr, u2.other _ (by decide), u2.gpr, or_eq_zero, e1, m1]
    have hz : BitVec.ofNat 64 (s.mem (ch + BitVec.ofNat 64 (32 + n))).toNat = 0 ↔
        s.mem (ch + BitVec.ofNat 64 (32 + n)) = 0 := by
      constructor
      · intro h
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
        exact this
      · intro h; rw [h]; rfl
    rw [hz]
    constructor
    · rintro ⟨⟨h0, hl⟩, hb⟩
      exact ⟨h0, fun i hi => if e : i = n then e ▸ hb else hl i (by omega)⟩
    · rintro ⟨h0, hl⟩
      exact ⟨⟨h0, fun i hi => hl i (by omega)⟩, hl n (by omega)⟩

/-- **`challengeHigh`**: `r8` zero exactly when the challenge's top 32 bytes are. -/
theorem challengeHigh_ok {ch : Addr} {s : State} (h31 : s.gpr .r31 = ch)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 (32 + i)) 1) :
    WP isa (.block challengeHigh) s fun t =>
      Rest [.r8, .r9] s t ∧ t.mem = s.mem ∧
      (t.gpr .r8 = 0 ↔ ∀ i < 32, s.mem (ch + BitVec.ofNat 64 (32 + i)) = 0) := by
  unfold challengeHigh
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (challengeOr_ok (ch := ch) 32 (Nat.le_refl _) s1 (by rw [u1.other _ (by decide), h31])
    (by rw [u1.rd, u1.wr]; exact hin)) fun t ⟨rt, mt, et⟩ =>
      ⟨(u1.rest (by decide)).trans rt, by rw [mt, u1.mem], ?_⟩
  rw [et, u1.gpr, u1.mem]
  simp

/-- The static of the cached `-[1]B … -[15]B` at `T`: readable, its words, not wrapping around,
apart from the working space. -/
structure BStat (b T : Addr) (s : State) : Prop where
  rd : (⟨T, 1920⟩ : Region) ∈ s.rd
  fit : T.toNat + 1920 ≤ 2 ^ 64
  words : ∀ q < 240, s.mem.readW (T + BitVec.ofNat 64 (8 * q)) 64 = bWord q
  ws : (⟨T, 1920⟩ : Region).Disjoint ⟨b, 8192⟩

/-- The static's facts through a frame within the working space. -/
theorem BStat.of_frame {T : Addr} {s t : State} (h : BStat b T s) (hrd : t.rd = s.rd) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩) : BStat b T t where
  rd := hrd ▸ h.rd
  fit := h.fit
  words q hq := by
    rw [← h.words q hq]
    exact hf.readW (r := ⟨T, 1920⟩) (Offset.contains_base T (by omega) (by omega))
      (fun r hr x h₁ h₂ => h.ws x h₁ (hs r hr x h₂)) (by decide)
  ws := h.ws

/-- **`[k] A - [S] B` compared with `-R`**, for the decoded `A` and `R` in the tables at 7776 and
7904 and the static at `s.syms bSym`, as the equation `[S] B = R + [k] A`: what the windows'
proof gives (`Proof/Ed25519/PPC64LE/WindowRhs.lean`, `rhs_ok`). -/
def RhsOk : Prop := ∀ {b pk sig ch : Addr} {s : State} {PK RS : List Byte},
  VCtx b pk sig ch s → BStat b (s.syms bSym) s →
  Spec.Ed25519.decodePoint PK = some (tableAt s.mem b 7776) →
  Spec.Ed25519.decodePoint RS = some (tableAt s.mem b 7904) →
  WP isa verifyRhs s fun t => Rest (.r17 :: sideR) s t ∧ Frame (sideW b 8032) s.mem t.mem ∧
    t.gpr .r17 = if Spec.Ed25519.pointEqual
      (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32)) Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd (tableAt s.mem b 7904)
        (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem ch 64)) (tableAt s.mem b 7776))) then 1 else 0

end

end VG.Proof.Ed25519.PPC64LE
