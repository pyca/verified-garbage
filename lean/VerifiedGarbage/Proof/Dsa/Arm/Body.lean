module

public import VerifiedGarbage.Proof.Dsa.Arm.Compute
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Bytes
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on 32-bit ARM: the bodies of signing and verifying

After the computation, signing writes r and s to the caller's output under
the flag (`writeScalar_ok`: zeros unless every check passed), and both
return the flag's low bit (`result_ok`). `signBody_ok` and `verifyBody_ok`
start from a flag of all ones, as the public checks of the domain's shape
leave it when they pass.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- The caller's output, of `len` bytes, apart from the working space. -/
structure Output (s : State) (base : Addr) (size len : Nat) : Prop where
  fits : (pointerValue base s (.input .out)).toNat + len ≤ 2 ^ 32
  writes : ∀ e k, e + k ≤ len → InRegions s.wr (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 e) k
  apart : Region.Disjoint ⟨State.addr (pointerValue base s (.input .out)), len⟩ ⟨base, size⟩

/-- What a body keeps: the registers but `coreClob`, and the memory but the
working space's computed values and the output. -/
structure Body (base P : Addr) (L : Nat) (s t : State) : Prop where
  rest : Rest coreClob s t
  mem : ∀ x, (∀ r ∈ runRanges, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) → L ≤ ofs P x → t.mem x = s.mem x

theorem Body.of_run {base P : Addr} {L : Nat} {s t : State} (Rn : Run base s t) : Body base P L s t :=
  ⟨Rn.rest, fun x h _ => Rn.mem x h⟩

theorem Body.trans {base P : Addr} {L : Nat} {s t u : State} (h₁ : Body base P L s t) (h₂ : Body base P L t u) :
    Body base P L s u :=
  ⟨h₁.rest.trans h₂.rest, fun x h h' => (h₂.mem x h h').trans (h₁.mem x h h')⟩

theorem Output.run {s t : State} {base : Addr} {size len : Nat} (O : Output s base size len) (Rn : Run base s t) :
    Output t base size len := by
  have P := pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem (by decide) (p := .input .out) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  exact ⟨by rw [P]; exact O.fits, by rw [P, Rn.rest.wr]; exact O.writes, by rw [P]; exact O.apart⟩

theorem Output.next {s t : State} {base : Addr} {size len o l : Nat} (O : Output s base size len)
    (St : Stage base s t o l) (ho : o = 116 ∧ l = 4 ∨ 4960 ≤ o ∧ o + l ≤ 15712) : Output t base size len :=
  O.run (St.run ho)

theorem Outs.arith_run {base : Addr} {m m' : Mem} (O : Outs base arithRanges m m') : Outs base runRanges m m' :=
  fun x hx => O x fun r hr => by
    have h₁ := hx (0, 64) (by simp [runRanges])
    have h₃ := hx (256, 15456) (by simp [runRanges])
    simp only [arithRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only at h₁ h₃
    rcases hr with rfl | rfl <;> simp only <;> omega

/-- The flag's low bit. -/
theorem result_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (acc : Prop) [Decidable acc] (hm : maskW base s = mask32 acc) :
    WP isa (.block SignVerify.result) s fun t =>
      t.gpr .r0 = (if acc then 1 else 0) ∧ Rest [.r0] s t ∧ t.mem = s.mem := by
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  refine wp_ldr (by decide) (hs.ea12 (by omega)) (hs.read (by omega)) fun t₁ u₁ => wp_dp (op2_imm (by decide))
    fun t u₂ => WP.block_nil ⟨?_, (u₁.rest (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, u₁.mem]⟩
  have m : s.mem.readW (off base 116) 32 = mask32 acc := hm
  rw [u₂.gpr, dpVal, u₁.gpr, show Impl.Dsa.Arm.Layout.field .mask = 116 from rfl, m]
  by_cases h : acc <;> simp only [mask32, h, ↓reduceIte] <;> decide

/-- Bytes at a pointer apart from a range that alone changed. -/
theorem bytes_keep {m m' : Mem} {q p : Addr} {len k : Nat} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p k = Spec.Rsa.bytesAt m p k := by
  unfold Spec.Rsa.bytesAt
  exact List.map_congr_left fun i hi => VG.Proof.Weierstrass.keep_of_disjoint' h hd hl (List.mem_range.mp hi) hk

/-- A part of the output that alone changed keeps the rest of memory. -/
theorem Body.of_out {base P : Addr} {L e l : Nat} {s t : State} (R : Rest coreClob s t)
    (O : Outside (P + BitVec.ofNat 64 e) 0 l s.mem t.mem) (he : e + l ≤ L) (hL : L ≤ 2 ^ 64) :
    Body base P L s t :=
  ⟨R, fun x _ h' => O x (.inr (by
    have H := Offset.lt_iff x P (d := e) (n := l) (by omega)
    have : ¬ (x - (P + BitVec.ofNat 64 e)).toNat < l := fun h => by have := H.mp h; simp only [ofs] at h'; omega
    simp only [ofs]
    omega))⟩

theorem writeScalar_ok {s : State} {base : Addr} {size qLen nQ input v : Nat} (hs : Ws s base size)
    (hz : 15712 < size) (wq : Width qLen nQ) (q32 : qLen ≤ 32) (hin : 4960 ≤ input) (hin' : input + qLen ≤ 15712)
    (hv : localVal base s input qLen = v) (hvl : v < 256 ^ qLen)
    (acc : Prop) [Decidable acc] (hm : maskW base s = mask32 acc) (O : Output s base size (2 * qLen)) (second : Bool) :
    WP isa (SignVerify.writeScalar qLen input second) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out)) +
          BitVec.ofNat 64 (if second then qLen else 0)) qLen =
        (if acc then Spec.Dsa.encodeBE qLen v else List.replicate qLen 0) ∧
      maskW base t = maskW base s ∧
      pointerValue base t (.input .out) = pointerValue base s (.input .out) ∧ t.wr = s.wr ∧
      KeepsLocals base s t 4960 15712 ∧
      (∀ e k, e + k ≤ 2 * qLen → (e + k ≤ (if second then qLen else 0) ∨ (if second then qLen else 0) + qLen ≤ e) →
        Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 e) k =
          Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 e) k) ∧
      Body base (State.addr (pointerValue base s (.input .out))) (2 * qLen) s t := by
  obtain ⟨n0, n48, hl, hl'⟩ := wq.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  have nw := hs.nowrap
  have q4 := wq.four
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  unfold SignVerify.writeScalar
  dsimp only
  rw [← wq.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 8) hs (by omega) wq (by decide)
    (localReady (o := input) (len := qLen) hs hin (by omega) (by omega))) fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  rw [local_operand hs (by omega), hv] at Vu
  have Ku : Outs base arithRanges s.mem u.mem := Outs.of_slot (i := 8) Ou (by decide) n48
  have Pu : pointerValue base u (.input .out) = pointerValue base s (.input .out) :=
    pointerValue_keep (Ru.gpr .r12 (by decide)) Ku arith_hdr (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  have mu : maskW base u = maskW base s := maskW_arith Ku
  have hP32 : (pointerValue base s (.input .out)).toNat + 2 * qLen ≤ 2 ^ 32 := O.fits
  -- The pointer: `out`, or `out + qLen`.
  have ptr : WP isa (.block (SignVerify.outputPointer qLen second ++ [.ldr .r3 .r12 (Impl.Dsa.Arm.Layout.field .mask)])) u
      fun w => w.gpr .r11 = pointerValue base s (.input .out) + BitVec.ofNat 32 (if second then qLen else 0) ∧ w.gpr .r3 = mask32 acc ∧
        Rest [.r3, .r4, .r11] u w ∧ w.mem = u.mem := by
    simp only [SignVerify.outputPointer, List.append_assoc]
    refine VG.Proof.X25519.Arm.WP.append (pointer_ok wu (by omega) (p := .input .out)
      (by decide : Impl.Dsa.Layout.Field.out ≠ .mask))
      fun w₁ ⟨P₁, R₁, M₁⟩ => ?_
    rw [Pu] at P₁
    have w₁s := wu.of_rest R₁ (by decide)
    cases second
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      refine wp_ldr (by decide) (w₁s.ea12 (by omega)) (w₁s.read (by omega)) fun w u₂ => WP.block_nil
        ⟨by rw [u₂.other .r11 (by decide), P₁]; exact (BitVec.add_zero _).symm, ?_,
          (R₁.mono (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, M₁]⟩
      rw [u₂.gpr, M₁, fm]; exact mu.trans hm
    · simp only [↓reduceIte, List.cons_append, List.nil_append]
      refine wp_movw fun w₂ u₂ => wp_dp (op2_reg _ _) fun w₃ u₃ => ?_
      have w₃s := (w₁s.of_upd u₂ (by decide)).of_upd u₃ (by decide)
      refine wp_ldr (by decide) (w₃s.ea12 (by omega)) (w₃s.read (by omega)) fun w u₄ => WP.block_nil
        ⟨?_, ?_, (((R₁.mono (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
          (u₄.rest (by decide)),
          by rw [u₄.mem, u₃.mem, u₂.mem, M₁]⟩
      · rw [u₄.other .r11 (by decide), u₃.gpr, dpVal, u₂.other .r11 (by decide), u₂.gpr, P₁, movw_ofNat (by omega)]
      · rw [u₄.gpr, u₃.mem, u₂.mem, M₁, fm]; exact mu.trans hm
  refine WP.seq (WP.mono ptr fun w ⟨Pw, Cw, Rw, Mw⟩ => ?_)
  have ww := wu.of_rest Rw (by decide)
  have off32 : (if second then qLen else 0) + qLen ≤ 2 * qLen := by split <;> omega
  have addr : State.addr (w.gpr .r11) = State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 (if second then qLen else 0) := by
    rw [Pw, VG.Arm.addr_add (by omega)]
  have hc : w.gpr .r3 = if decide acc then BitVec.allOnes 32 else 0 := by
    rw [Cw]; by_cases h : acc <;> simp [mask32, h]
  have wr : w.wr = s.wr := by rw [Rw.wr, Ru.wr]
  refine WP.mono (storeComponent_ok (input := baseS nQ) (len := qLen) ww (decide acc) hc
    (by simp only [baseS]; omega) (by simp only [baseS]; omega) q4 wq.word
    (by rw [Pw, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by split <;> omega : (if second then qLen else 0) < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (fun e k hek => by rw [addr, Offset.add_add, wr]; exact O.writes _ _ (by omega))
    (by
      rw [addr]
      exact ((O.apart.sub_left (Offset.sub_base (State.addr (pointerValue base s (.input .out))) off32)).sub_right
        (Offset.sub_base base (by simp only [baseS]; omega))).symm)) fun t ⟨wt, Vt, Rt, Ot⟩ => ?_
  rw [addr] at Vt Ot
  have dis : ∀ d k, d + k ≤ size → Region.Disjoint ⟨off base d, k⟩
      ⟨State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 (if second then qLen else 0), qLen⟩ :=
    fun d k h => ((O.apart.sub_left (Offset.sub_base (State.addr (pointerValue base s (.input .out))) off32)).sub_right
      (Offset.sub_base base h)).symm
  have rw32 : ∀ d, d + 4 ≤ size → t.mem.readW (off base d) 32 = u.mem.readW (off base d) 32 := fun d h => by
    rw [← Mw]
    exact (Mem.readW_congr fun i hi =>
      (VG.Proof.Weierstrass.keep_of_disjoint' Ot (dis d 4 h) (by omega) hi (by decide)).symm).symm
  refine ⟨?_, ?_, ?_, by rw [Rt.wr, wr], ?_, ?_, ?_⟩
  · rw [Vt, Mw]
    have e : val32 u.mem base (baseS nQ) (qLen / 4) = v := by
      rw [val32_prefix_of_lt (n := 2 * nQ) (by omega) (by
        rw [show baseS nQ = slot nQ 8 from rfl, Vu, ← pow256_words wq.word]; exact hvl)]
      exact Vu
    rw [e]
    by_cases h : acc <;> simp [h]
  · exact (rw32 116 (by omega)).trans mu
  · exact (rw32 96 (by omega)).trans Pu
  · intro o len h₁ h₂
    rw [Arm.localVal, Arm.localVal, bytes_keep Ot (dis o len (by omega)) (by omega) (by omega), Mw,
      outs_bytes Ku (by omega) (by decide) fun r hr => by
        simp only [arithRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint base (.inr (by omega)) (by omega) (by omega)]
  · intro e k hek hsep
    have Pf := O.fits
    rw [bytes_keep Ot (Offset.disjoint _ hsep (by omega) (by omega)) (by omega) (by omega), Mw,
      outs_bytes Ku (by omega) (by decide) fun r hr => by
        simp only [arithRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          exact (O.apart.sub_left (Offset.sub_base _ hek)).sub_right (Offset.sub_base base (by omega))]
  · exact (Body.of_run (Run.mk Ru (Outs.arith_run Ku))).trans
      (Body.of_out ((Rw.mono (by decide)).trans (Rt.mono (by decide))) (by rw [Mw] at Ot; exact Ot) off32 (by omega))

theorem Output.keep {s t : State} {base : Addr} {size len : Nat} (O : Output s base size len)
    (hp : pointerValue base t (.input .out) = pointerValue base s (.input .out)) (hw : t.wr = s.wr) :
    Output t base size len :=
  ⟨by rw [hp]; exact O.fits, by rw [hp, hw]; exact O.writes, by rw [hp]; exact O.apart⟩

theorem signBody_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1)
    (hm : maskW base s = BitVec.allOnes 32) (O : Output s base size (2 * qLen)) :
    WP isa (SignVerify.signBody pLen qLen) s fun t =>
      t.gpr .r0 = (if signChecks P Q G Y X K D then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out))) (2 * qLen) =
        (if signChecks P Q G Y X K D then
          Spec.Dsa.encodeBE qLen (rValue P Q G K) ++ Spec.Dsa.encodeBE qLen (sValue P Q G X K D)
        else List.replicate (2 * qLen) 0) ∧
      Body base (State.addr (pointerValue base s (.input .out))) (2 * qLen) s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := Sc.lens
  have big := Sc.big
  have Qlt := operand_lt_of Iq
  have qlt : ∀ x, x % Q < 256 ^ qLen := fun x => Nat.lt_trans (Nat.mod_lt _ (by omega)) Qlt
  have Lr : Impl.Dsa.Layout.r = 14720 := rfl
  have Ls : Impl.Dsa.Layout.s = 14752 := rfl
  unfold SignVerify.signBody
  refine WP.seq (WP.mono (signCompute_ok Sc Ip Iq Ig Iy Ix Ik Id hc hP hPo hQ hQo) fun u ⟨Fu, Ru, Su, Rn⟩ => ?_)
  have mu : maskW base u = mask32 (signChecks P Q G Y X K D) := by
    rw [Fu, hm, BitVec.allOnes_and]
  have Pu : pointerValue base u (.input .out) = pointerValue base s (.input .out) :=
    pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem (by decide) (by decide : Impl.Dsa.Layout.Field.out ≠ .mask)
  have Ou := O.run Rn
  have wu := Rn.ws Sc.ws
  refine WP.seq (WP.mono (writeScalar_ok wu big Sc.wq q32 (by omega) (by omega) Ru (by simp only [rValue]; exact qlt _)
    _ mu Ou false) fun v ⟨Bv, mv, Pv, Wv, Kv, _, Bdv⟩ => ?_)
  have wv := wu.of_rest Bdv.rest (by decide)
  refine WP.seq (WP.mono (writeScalar_ok (v := sValue P Q G X K D) wv big Sc.wq q32 (by omega) (by omega)
    (by rw [Kv _ _ (by omega) (by omega)]; exact Su) (by simp only [sValue]; exact qlt _) _ (mv.trans mu)
    (Ou.keep Pv Wv) true) fun w ⟨Bw, mw, Pw, Ww, Kw, Ew, Bdw⟩ => ?_)
  have ww := wv.of_rest Bdw.rest (by decide)
  refine WP.mono (result_ok ww (by omega) _ ((mw.trans mv).trans mu)) fun t ⟨r0, Rt, Mt⟩ => ⟨r0, ?_, ?_⟩
  · rw [Pu] at Bv
    rw [Pv, Pu] at Bw
    simp only [Bool.false_eq_true, ↓reduceIte] at Bv Bw
    rw [Mt]
    refine VG.Proof.Dsa.signatureBytes _ ?_ Bw
    have E := Ew 0 qLen (by omega) (.inl (by simp only [↓reduceIte]; omega))
    rw [Pv, Pu, BitVec.add_zero] at E
    rw [E]
    simpa only [BitVec.add_zero] using Bv
  · rw [Pu] at Bdv
    rw [Pv, Pu] at Bdw
    exact ((Body.of_run Rn).trans Bdv).trans (Bdw.trans ⟨Rt.mono (by decide), fun x _ _ => by rw [Mt]⟩)

theorem verifyBody_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y R S D c : Nat}
    (Sc : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ir : Input s base size (.input .signature) qLen R) (Is : Input s base size .signatureS qLen S)
    (Id : Input s base size (.input .digest) c D) (hc : countValue base s Core.digestPrefix = c)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1)
    (hm : maskW base s = BitVec.allOnes 32) :
    WP isa (SignVerify.verifyBody pLen qLen) s fun t =>
      t.gpr .r0 = (if verifyChecks P Q G Y R S D then 1 else 0) ∧ Run base s t := by
  have big := Sc.big
  unfold SignVerify.verifyBody
  refine WP.seq (WP.mono (verifyCompute_ok Sc Ip Iq Ig Iy Ir Is Id hc hP hPo hQ hQo) fun u ⟨Fu, Rn⟩ => ?_)
  refine WP.mono (result_ok (Rn.ws Sc.ws) (by omega) _ (by rw [Fu, hm, BitVec.allOnes_and])) fun t ⟨r0, Rt, Mt⟩ =>
    ⟨r0, Rn.trans ⟨Rt.mono (by decide), fun x _ => by rw [Mt]⟩⟩

end VG.Proof.Dsa.Arm
