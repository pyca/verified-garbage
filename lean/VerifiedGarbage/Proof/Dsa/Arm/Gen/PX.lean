module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PHash
public import VerifiedGarbage.Proof.Dsa.Generation.Contributions
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory

/-! # DSA parameter generation on ARMv7: X

`pHashes m` (`pHashes_vp`): the first `m` hashes of X, each just below the
one before, in one claim (`accB`) whose value is the sum of the
contributions (`accB_value`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_dp wp_ldrb wp_strb op2_imm dpVal)
open VG.Proof.Ffdh.ParameterCandidate (topCut topByte)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Dsa.Generation (contributions pDigest)

section
variable {G : GP} {Gh : Hash}

/-- Hash `j` of X, from the seed at `k` and the offset `off`. -/
abbrev hX (HO : HashOk Gh) (G : GP) (k off j : Nat) : List Byte := HO.H (seedPlus G (seedAt G k) (off + j))

/-- The first `m` hashes of X, the last first. -/
def accB (HO : HashOk Gh) (G : GP) (k off : Nat) : Nat → List Byte
  | 0 => []
  | m + 1 => hX HO G k off m ++ accB HO G k off m

/-- Where the first `m` hashes of X start. -/
abbrev pStart (G : GP) (m : Nat) : Nat := sX + G.pLen - m * G.qLen

theorem accB_length (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen) :
    ∀ m, (accB HO G k off m).length = m * G.qLen
  | 0 => by simp [accB]
  | m + 1 => by rw [accB, List.length_append, hl, accB_length HO hl m, Nat.succ_mul]; omega_arith

theorem accB_value (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen) :
    ∀ m, Spec.Dsa.decodeBE (accB HO G k off m) = contributions (8 * G.qLen) (pDigest (8 * G.qLen) (seedAt G k) off) m
  | 0 => rfl
  | m + 1 => by
    rw [accB, VG.Proof.Dsa.Generation.prepend_digest, accB_value HO hl hH hsl m,
      VG.Proof.Dsa.Generation.contributions_succ, accB_length HO hl m]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (m * G.qLen) = m * (8 * G.qLen) by
      rw [Nat.mul_left_comm]]
    congr 1
    simp only [hX, hH, pDigest, seedPlus, hsl, Nat.add_assoc]

/-- Other claims, which the memory holds. -/
theorem SS.reclaim {σ s : State} {c : Cfg} (h : SS G σ c s) {cl' : Claims}
    (hcl : ∀ x ∈ cl', Spec.Rsa.bytesAt s.mem (G.sa x.1) x.2.length = x.2 ∧ x.1 + x.2.length ≤ sK G.pLen) :
    SS G σ { c with cl := cl' } s :=
  ⟨h.gi, h.r7, h.r8, h.r9, fun x hx => (hcl x hx).1, fun x hx => (hcl x hx).2, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

/-- Two claims side by side, as one. -/
theorem SB.join {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {a b : List Byte} (ha : (o, a) ∈ cl)
    (hb : (o + a.length, b) ∈ cl) : Spec.Rsa.bytesAt m (G.sa o) (a ++ b).length = a ++ b := by
  rw [List.length_append, VG.Proof.Dsa.Generation.bytesAt_append, h _ ha]
  have e : VG.Proof.Bignum.off (G.sa o) a.length = G.sa (o + a.length) := by
    simp only [VG.Proof.Bignum.off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e, h _ hb]

/-- The claims during X. -/
abbrev pCfg (c : Cfg) (HO : HashOk Gh) (G : GP) (k off m : Nat) (rest : Claims) : Cfg :=
  { c with cl := (G.qLen, padTail HO.md G.qLen) :: (pStart G m, accB HO G k off m) :: rest }

/-- The first `m` hashes of X. -/
theorem pHashes_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off n : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hn : n < 256) (hoff : off + n < 2 ^ 24)
    (hnq : n * G.qLen ≤ G.pLen + 96) {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart 0 96 x ∧ Apart sA 112 x ∧ Apart (pStart G n) (n * G.qLen) x) :
    ∀ m ≤ n, VP (St G (pCfg c HO G k off 0 rest) X) (g.pHashes m) (St G (pCfg c HO G k off m rest) X)
  | 0, _ => VP.block_nil fun _ _ h => h
  | m + 1, hm => by
    have ih := pHashes_vp (X := X) HO hlq hp hq hk4 hsb hk hS hSv hO hOv hn hoff hnq hrest m (by omega_arith)
    refine VP.seq ih ?_
    have hXv : sX = 192 := rfl
    have hAv : sA = 4096 := rfl
    have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
    have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
      rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
    have al := accB_length HO hHl m
    have hm1 : (m + 1) * G.qLen = m * G.qLen + G.qLen := Nat.succ_mul _ _
    have hmn : (m + 1) * G.qLen ≤ n * G.qLen := Nat.mul_le_mul_right _ hm
    have e1 : pStart G (m + 1) + G.qLen = pStart G m := by
      simp only [pStart]; omega_arith
    refine (pHash_vp (c := pCfg c HO G k off m rest) (j := m) HO hlq hp hq hk4 hsb hk hS hSv hO hOv (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by simp) (cl' := (pStart G m, accB HO G k off m) :: rest) fun x hx => ?_).mono
      (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.reclaim fun y hy => ?_, x⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨by simp, ?_, ?_, ?_⟩ <;> simp only [Apart, al, pStart] <;> omega_arith
      · obtain ⟨a, b, d⟩ := hrest x hx
        refine ⟨by simp [hx], a, b, ?_⟩
        simp only [Apart, pStart] at d ⊢
        omega_arith
    · have sb := h.sb
      have cl := h.clOk
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact ⟨sb _ (by simp), cl _ (by simp)⟩
      · have j := sb.join (o := pStart G (m + 1)) (a := hX HO G k off m) (b := accB HO G k off m)
          (by simp [pStart]) (by rw [hHl, e1]; simp)
        refine ⟨j, ?_⟩
        show pStart G (m + 1) + (accB HO G k off (m + 1)).length ≤ _
        rw [accB_length HO hHl]
        simp only [pStart]; omega_arith
      · exact ⟨sb _ (by simp [hy]), cl _ (by simp [hy])⟩

theorem top_memory {m : Mem} {op : Addr} {n : Nat} (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW op (m op ||| 128#8)) op n = topCut (Spec.Rsa.bytesAt m op n) 7 := by
  have hne : Spec.Rsa.bytesAt m op n ≠ [] := by
    intro h; have := bytesAt_length' m op n; rw [h] at this; simp at this; omega_arith
  apply List.ext_getElem
  · rw [bytesAt_length', VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, bytesAt_length']
  · intro i hi hi'
    have hil : i < n := by simpa only [bytesAt_length'] using hi
    have hget : (topCut (Spec.Rsa.bytesAt m op n) 7)[i] = (topCut (Spec.Rsa.bytesAt m op n) 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, VG.Proof.Ffdh.ParameterCandidate.topCut_getD, VG.Proof.Dsa.Generation.topByte_seven]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeW8_apply]
    by_cases hiz : i = 0
    · subst i; simp [show 0 < n by omega_arith]
    · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
        simpa using Offset.add_ofNat_ne op (by omega_arith : i < 2 ^ 64) (by decide : 0 < 2 ^ 64) hiz
      simp [hiz, hne0, hil]

/-- X's top bit set. -/
theorem topX_vp {P Q : State → State → Prop} {c : State → Cfg} {L N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G σ (c σ) s) (hL : L = G.pLen) (hN : 1 ≤ N) (hN' : sX + N ≤ sK G.pLen)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sX) N = bs)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r12] s t → Frame [G.rs sX N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sX) N = topCut bs 7 → Q σ t) :
    VP P (.block (scr L .r0 sX ++ ([.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0] : List Instr))) Q := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sX ++ [.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).r8, (hF _ _ h₂).r8]
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  refine scr_ok (d := .r0) h.r8 rfl h.lens (by omega_arith) fun s₁ v₁ R₁ M₁ => ?_
  have aq := h.addr (o := sX) (n := N) (by omega_arith) (by omega_arith)
  have c0 : (G.rs sX N).Contains (G.sa sX) 1 := by
    show (_ - _ : Addr).toNat + 1 ≤ N
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  have w0 : InRegions s.wr (G.sa sX) 1 :=
    Covers.one (gi.inScr (o := sX) (n := N) (by omega_arith)) _ _ ⟨_, List.mem_singleton_self _, c0⟩
  have r0 : InRegions (s.rd ++ s.wr) (G.sa sX) 1 := let ⟨r, hr, hc⟩ := w0; ⟨r, List.mem_append_right _ hr, hc⟩
  have a0 : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0) = G.sa sX := by rw [BitVec.add_zero, v₁, aq]
  refine wp_ldrb (by decide) a0 (by rw [R₁.rd, R₁.wr]; exact r0) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_strb (a := G.sa sX) (by decide) (by rw [u₃.other .r0 (by decide), u₂.other .r0 (by decide)]; exact a0)
    (by rw [u₃.wr, u₂.wr, R₁.wr]; exact w0) fun t u₄ => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r12] s t := ((R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))).trans
    (u₄.rest _)
  have mt : t.mem = s.mem.writeW (G.sa sX) (s.mem (G.sa sX) ||| 128#8) := by
    rw [u₄.mem, u₃.mem, u₂.mem, M₁, u₃.gpr, dpVal, u₂.gpr, M₁, orr_byte]; rfl
  refine k σ s t hs R ?_ ?_
  · rw [mt]
    exact (Frame.refl [G.rs sX N] s.mem).writeW List.mem_cons_self (w := 8) _ c0
  · rw [mt, top_memory hN (by omega_arith), hb σ s hs]

/-- `(L − 1) / N`, the number of whole hashes below X's top one. -/
abbrev cnt (G : GP) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

/-- X's bytes: the low `pLen` bytes of the hashes, the top bit set. -/
abbrev xBytes (HO : HashOk Gh) (G : GP) (k off : Nat) : List Byte :=
  topCut ((accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen)) 7

theorem decodeBE_drop (bs : List Byte) (d : Nat) :
    Spec.Dsa.decodeBE (bs.drop d) = Spec.Dsa.decodeBE bs % 256 ^ (bs.length - d) := by
  have e := VG.Proof.Dsa.decodeBE_append (bs.take d) (bs.drop d)
  rw [List.take_append_drop, List.length_drop] at e
  rw [e, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := VG.Proof.Dsa.decodeBE_lt (bs.drop d); rwa [List.length_drop] at this)]

/-- X's value. -/
theorem xBytes_value {A : List Byte} {d n : Nat} (hA : A.length = d + n) (hn : 1 ≤ n) :
    Spec.Dsa.decodeBE (topCut (A.drop d) 7) = Spec.Dsa.decodeBE A % 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
  have hne : A.drop d ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop] at this; simp at this; omega_arith
  rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.topCut_value hne (by decide),
    ← VG.Proof.Dsa.decodeBE_os2ip, decodeBE_drop, List.length_drop, hA,
    show d + n - d = n by omega_arith, show 8 * (n - 1) + 7 = 8 * n - 1 by omega_arith,
    show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul],
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_arith))]

/-- The candidate p of the spec, from X's value. -/
theorem pCandidate_xBytes (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hp1 : 1 ≤ G.pLen) (hc : G.pLen ≤ (cnt G + 1) * G.qLen) (q : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) q (seedAt G k) off =
      Spec.Dsa.decodeBE (xBytes HO G k off) + 1 - Spec.Dsa.decodeBE (xBytes HO G k off) % (2 * q) := by
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega_arith) hlen,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega_arith),
    VG.Proof.Dsa.Generation.pReduction_orOne, xBytes,
    xBytes_value (by rw [accB_length HO hl]; omega_arith) hp1, accB_value HO hl hH hsl]

/-- X, from the seed at `k` and the offset `off`, at `sX`. -/
theorem pX_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hoff : off + (cnt G + 1) < 2 ^ 24)
    {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart 0 96 x ∧ Apart sA 112 x ∧ Apart (pStart G (cnt G + 1)) ((cnt G + 1) * G.qLen) x) :
    VP (St G (pCfg c HO G k off 0 rest) X) g.pX
      (St G { c with cl := (G.qLen, padTail HO.md G.qLen) :: (sX, xBytes HO G k off) :: rest } X) := by
  have hc : (cnt G + 1) * G.qLen ≤ G.pLen + 96 ∧ G.pLen ≤ (cnt G + 1) * G.qLen ∧ cnt G + 1 < 256 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  have hcount : g.count = cnt G := by simp only [Geo.count, hp, hq]
  have hXv : sX = 192 := rfl
  have hAv : sA = 4096 := rfl
  have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  have al := accB_length HO hHl (cnt G + 1)
  have hd : pStart G (cnt G + 1) + ((cnt G + 1) * G.qLen - G.pLen) = sX := by simp only [pStart]; omega_arith
  unfold Geo.pX
  rw [hcount, hp]
  refine VP.seq (pHashes_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hc.2.2 (by omega_arith) hc.1 hrest _ (Nat.le_refl _)) ?_
  refine topX_vp (c := fun _ => pCfg c HO G k off (cnt G + 1) rest) (fun σ s h => h.1) rfl (N := G.pLen)
    (by omega_arith) (by omega_arith) (bs := (accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen))
    (fun σ s ⟨h, _⟩ => ?_) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
  · have b := h.sb (pStart G (cnt G + 1), accB HO G k off (cnt G + 1)) (by simp)
    simp only at b
    rw [al] at b
    have a : G.sa sX = G.sa (pStart G (cnt G + 1)) + BitVec.ofNat 64 ((cnt G + 1) * G.qLen - G.pLen) := by
      simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, hd]
    rw [a, bytesAt_slice' _ _ (len := (cnt G + 1) * G.qLen) (by omega_arith), b, List.take_of_length_le (by
      rw [List.length_drop, al]; omega_arith)]
  refine h.of_scr R (o := sX) (n := G.pLen) (by omega_arith) (f.mono (by simp)) fun y hy => ?_
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inl ⟨by simp, .inl (by simp only [padTail_length HO.md (show G.qLen < 56 by omega_arith) HO.hL]; omega_arith)⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · have hl : (xBytes HO G k off).length = G.pLen := by
      rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
        rw [← List.length_pos_iff, List.length_drop, al]; omega_arith), List.length_drop, al]; omega_arith
    exact .inr ⟨by rw [hl]; exact e, by rw [hl]; omega_arith⟩
  · obtain ⟨_, _, d⟩ := hrest y hy
    exact .inl ⟨by simp [hy], by simp only [Apart, pStart] at d ⊢; omega_arith⟩

end

end VG.Proof.Dsa.Arm.Gen
