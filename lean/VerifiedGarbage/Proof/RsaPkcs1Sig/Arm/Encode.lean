module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# EMSA-PKCS1-v1_5 encoding on ARMv7: correctness

`encode_ok`: from a state with the buffer, the hash value, the hash
function's number and the lengths in its registers (`EncIn`), `encode`
writes the encoding (`encOut`) to the buffer and sets `r3` to 1, or sets it
to 0 if there is none, changing memory only in the buffer and only the
registers `r0`–`r3` and `lr`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm Spec.RsaPkcs1Sig
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_strb wp_subs wp_cmp op2_imm op2_reg op2_lsr dpVal
  eval_ne eval_eq)

/-- The encoding of `D` for the hash function numbered `id`, if any. -/
def encOut (id : Nat) (D : List Byte) (k : Nat) : Option (List Byte) :=
  match Hash.ofId id with
  | some h => encode h D k
  | none => none

/-- What `encode` starts from. -/
structure EncIn (s : State) (dst src id : BitVec 32) (k dl : Nat) : Prop where
  r0 : s.gpr .r0 = dst
  r1 : s.gpr .r1 = src
  r2 : s.gpr .r2 = id
  r3 : s.gpr .r3 = BitVec.ofNat 32 k
  lr : s.gpr .lr = BitVec.ofNat 32 dl
  k64 : 64 ≤ k
  k1024 : k ≤ 1024
  dl32 : dl < 2 ^ 32
  dstFit : dst.toNat + k ≤ 2 ^ 32
  srcFit : src.toNat + dl ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) k
  read : InRegions (s.rd ++ s.wr) (State.addr src) dl
  sep : Region.Disjoint ⟨State.addr src, dl⟩ ⟨State.addr dst, k⟩

/-- What `encode` leaves. -/
def EncPost (s : State) (dst src id : BitVec 32) (k dl : Nat) (t : State) : Prop :=
  Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t ∧
    match encOut id.toNat (Spec.Rsa.bytesAt s.mem (State.addr src) dl) k with
    | some em => t.gpr .r3 = 1 ∧ Spec.Rsa.bytesAt t.mem (State.addr dst) k = em
    | none => t.gpr .r3 = 0

theorem fail_ok {s : State} :
    WP isa fail s fun t => t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t ∧ t.gpr .r3 = 0 :=
  wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨u.mem, u.rest (by simp), u.gpr⟩

/-- The bytes of the buffer written so far. -/
def Bytes (m : Mem) (a : Addr) (xs : List Byte) (n : Nat) : Prop := ∀ i < n, m (a + BitVec.ofNat 64 i) = xs.getD i 0

/-- A byte stored at index `n`. -/
theorem Bytes.store {m : Mem} {a : Addr} {xs : List Byte} {n : Nat} (h : Bytes m a xs n) (hn : n < 2 ^ 64) :
    Bytes (m.writeW (a + BitVec.ofNat 64 n) (xs.getD n 0)) a xs (n + 1) := by
  intro i hi
  rw [WriteBytes.writeW8_apply]
  by_cases e : i = n
  · subst e; simp
  · simp only [Offset.add_ofNat_ne a (by omega) hn e, ↓reduceIte]
    exact h i (by omega)

theorem Bytes.mono {m : Mem} {a : Addr} {xs : List Byte} {n n' : Nat} (h : Bytes m a xs n) (hn : n' ≤ n) :
    Bytes m a xs n' := fun i hi => h i (by omega)

/-- The encoding, once its checks pass. -/
def encList (h : Hash) (D : List Byte) (k : Nat) : List Byte :=
  [0, 1] ++ List.replicate (k - tLen h - 3) 0xff ++ [0] ++ (h.prefix ++ D)

theorem encList_length {h : Hash} {D : List Byte} {k : Nat} (hD : D.length = h.len) (hk : tLen h + 11 ≤ k) :
    (encList h D k).length = k := by
  simp only [encList, tLen, List.length_append, List.length_cons, List.length_nil, List.length_replicate, hD] at *
  omega

theorem encList_ps {h : Hash} {D : List Byte} {k i : Nat} (hi : i < k - tLen h - 3) :
    (encList h D k).getD (2 + i) 0 = 0xff := by
  simp only [encList, List.append_assoc]
  rw [getD_append_right _ _ _ (by simp), getD_append_left _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, show i < k - tLen h - 3 from hi]

theorem encList_mid {h : Hash} {D : List Byte} {k i : Nat} (hi : i < h.prefix.length + 1) :
    (encList h D k).getD (2 + (k - tLen h - 3) + i) 0 = (0 :: h.prefix).getD i 0 := by
  simp only [encList, List.append_assoc]
  rw [getD_append_right _ _ _ (by simp only [List.length_cons, List.length_nil]; omega),
    getD_append_right _ _ _ (by simp only [List.length_cons, List.length_nil, List.length_replicate]; omega)]
  simp only [List.length_cons, List.length_nil, List.length_replicate]
  rw [show 2 + (k - tLen h - 3) + i - (0 + 1 + 1) - (k - tLen h - 3) = i by omega]
  rcases i with _ | i
  · rfl
  · simp only [List.cons_append, List.getD_cons_succ, List.nil_append]
    rw [getD_append_left _ _ _ (by omega)]

theorem encList_D {h : Hash} {D : List Byte} {k i : Nat} :
    (encList h D k).getD (2 + (k - tLen h - 3) + (h.prefix.length + 1) + i) 0 = D.getD i 0 := by
  simp only [encList, List.append_assoc]
  rw [getD_append_right _ _ _ (by simp only [List.length_cons, List.length_nil]; omega),
    getD_append_right _ _ _ (by simp only [List.length_cons, List.length_nil, List.length_replicate]; omega)]
  simp only [List.length_cons, List.length_nil, List.length_replicate]
  rw [show 2 + (k - tLen h - 3) + (h.prefix.length + 1) + i - (0 + 1 + 1) - (k - tLen h - 3) =
    (h.prefix.length + i) + 1 by omega]
  simp only [List.cons_append, List.getD_cons_succ, List.nil_append]
  rw [getD_append_right _ _ _ (by omega)]
  congr 1; omega

theorem encode_eq {h : Hash} {D : List Byte} {k : Nat} :
    Spec.RsaPkcs1Sig.encode h D k =
      if D.length = h.len ∧ tLen h + 11 ≤ k then some (encList h D k) else none := by
  unfold Spec.RsaPkcs1Sig.encode encList
  simp only [digestInfo, List.length_append, tLen]
  by_cases h1 : D.length = h.len <;> by_cases h2 : h.prefix.length + h.len + 11 ≤ k <;> simp [h1, h2] <;> omega

/-! ## Writing the encoding -/

/-- A state of `write`: memory changed only in the buffer, whose first `n`
bytes are those of `L`. -/
structure Wr (s0 : State) (dst src : BitVec 32) (k : Nat) (L : List Byte) (n : Nat) (t : State) : Prop where
  frame : Frame [⟨State.addr dst, k⟩] s0.mem t.mem
  rest : Rest [.r0, .r1, .r2, .r3, .lr] s0 t
  r1 : t.gpr .r1 = src
  bytes : Bytes t.mem (State.addr dst) L n

section
variable {s0 t : State} {dst src id : BitVec 32} {k dl : Nat} {L : List Byte} {n : Nat}

theorem Wr.regs (h : Wr s0 dst src k L n t) {t' : State} (hg : ∀ r, r ∉ [Reg.r0, .r2, .r3, .lr] → t'.gpr r = t.gpr r)
    (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) :
    Wr s0 dst src k L n t' :=
  have sub : ∀ r : Reg, r ∈ [Reg.r0, .r2, .r3, .lr] → r ∈ [Reg.r0, .r1, .r2, .r3, .lr] := by decide
  ⟨hm ▸ h.frame, ⟨fun r hr => by rw [hg r (fun h' => hr (sub r h')), h.rest.gpr r hr], hrd.trans h.rest.rd,
    hwr.trans h.rest.wr, hsp.trans h.rest.sp⟩, by rw [hg .r1 (by decide)]; exact h.r1, hm ▸ h.bytes⟩

theorem Wr.upd (h : Wr s0 dst src k L n t) {t' : State} {d : Reg} {v : BitVec 32} (u : Upd t t' d v)
    (hd : d ∈ [Reg.r0, .r2, .r3, .lr]) : Wr s0 dst src k L n t' :=
  h.regs (fun r hr => u.other r fun e => hr (e ▸ hd)) u.mem u.rd u.wr u.sp

/-- `strb r2, [r0, #off]` of byte `n` of `L`. -/
theorem Wr.strb (h : Wr s0 dst src k L n t) (hin : EncIn s0 dst src id k dl) (hn : n < k)
    (hb : (t.gpr .r2).setWidth 8 = L.getD n 0) {off : Nat} (hoff : off < 4096)
    (hr0 : t.gpr .r0 + BitVec.ofNat 32 off = dst + BitVec.ofNat 32 n) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Wr s0 dst src k L (n + 1) t' → t'.gpr = t.gpr → WP isa (.block is) t' Q) :
    WP isa (.block (.strb .r2 .r0 off :: is)) t Q := by
  have hk := hin.k1024
  have ha : State.addr (dst + BitVec.ofNat 32 n) = State.addr dst + BitVec.ofNat 64 n :=
    addr_add (by have := hin.dstFit; omega)
  refine wp_strb hoff (a := State.addr dst + BitVec.ofNat 64 n) (by rw [hr0, ha]) ?_ fun t' u => kk t' ?_ u.gpr
  · rw [h.rest.wr]
    obtain ⟨r, hr, hc⟩ := hin.write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · refine ⟨?_, ⟨fun r hr => by rw [u.gpr]; exact h.rest.gpr r hr, u.rd.trans h.rest.rd, u.wr.trans h.rest.wr,
      u.sp.trans h.rest.sp⟩, by rw [u.gpr]; exact h.r1, ?_⟩
    · rw [u.mem]
      exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [u.mem, hb]
      exact h.bytes.store (by omega)

theorem setWidth_byte (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

/-- The bytes `bs` at `r0 + o`, … -/
theorem putBytes_ok (hin : EncIn s0 dst src id k dl) {b0 : Nat} :
    ∀ (bs : List Byte) (o : Nat) {n : Nat} {t : State}, Wr s0 dst src k L n t →
      t.gpr .r0 = dst + BitVec.ofNat 32 b0 → n = b0 + o → n + bs.length ≤ k →
      (∀ i < bs.length, L.getD (n + i) 0 = bs.getD i 0) → o + bs.length ≤ 4096 →
      ∀ {is : List Instr} {Q : State → Prop},
      (∀ t', Wr s0 dst src k L (n + bs.length) t' → (∀ r, r ≠ .r2 → t'.gpr r = t.gpr r) →
        WP isa (.block is) t' Q) →
      WP isa (.block (putBytes bs o ++ is)) t Q
  | [], _, n, t, h, _, _, _, _, _, _, _, kk => by
    simp only [putBytes, List.nil_append]
    exact kk t (by simpa using h) fun _ _ => rfl
  | b :: bs, o, n, t, h, r0, hn, hk, hL, ho, _, _, kk => by
    simp only [putBytes, List.cons_append]
    refine wp_mov (op2_imm (encodable_of_lt (by rw [BitVec.toNat_setWidth]; have := b.isLt; omega)))
      fun t1 u1 => ?_
    have h1 := h.upd u1 (by simp)
    refine h1.strb hin (by simp at hk; omega) (by rw [u1.gpr, setWidth_byte]; exact (hL 0 (by simp)).symm)
      (by simp at ho; omega) (by rw [u1.other _ (by decide), r0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hn])
      fun t2 h2 g2 => ?_
    refine putBytes_ok hin bs (o + 1) h2 (by rw [g2, u1.other _ (by decide), r0]) (by omega)
      (by simp at hk; omega) (fun i hi => by rw [show n + 1 + i = n + (i + 1) by omega, hL (i + 1) (by simp; omega)]; rfl)
      (by simp at ho; omega) fun t3 h3 g3 => kk t3 (by simpa [Nat.add_assoc, Nat.add_comm 1] using h3)
        fun r hr => by rw [g3 r hr, g2, u1.other r hr]

theorem Wr.start (hin : EncIn s0 dst src id k dl) : Wr s0 dst src k L 0 s0 :=
  ⟨Frame.refl _ _, Rest.refl _ _, hin.r1, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem prefix_le (h : Hash) : h.prefix.length ≤ 19 := by cases h <;> decide
theorem len_le (h : Hash) : h.len ≤ 64 := by cases h <;> decide
theorem len_pos (h : Hash) : 0 < h.len := by cases h <;> decide

/-- `write h`: the encoding of the hash value, `L`. -/
theorem write_ok {h : Hash} (hin : EncIn s0 dst src id k dl) (hD : dl = h.len) (hk : tLen h + 11 ≤ k) :
    WP isa (write h) s0 fun t => Frame [⟨State.addr dst, k⟩] s0.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s0 t ∧
      Bytes t.mem (State.addr dst) (encList h (Spec.Rsa.bytesAt s0.mem (State.addr src) dl) k) k ∧
      t.gpr .r3 = 1 := by
  have hk1 := hin.k1024
  have hpl := prefix_le h
  have hhl := len_le h
  have hhp := len_pos h
  have htl : tLen h = h.prefix.length + h.len := rfl
  generalize hDdef : Spec.Rsa.bytesAt s0.mem (State.addr src) dl = D
  have hDl : D.length = h.len := by rw [← hDdef, bytesAt_length, hD]
  have h0 : Wr s0 dst src k (encList h D k) 0 s0 := Wr.start hin
  unfold write
  rw [WP.seq_iff]
  -- `0x00 0x01`, and `PS`'s registers.
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  refine (h0.upd u1 (by simp)).strb hin (by omega_arith) (by rw [u1.gpr]; rfl) (by decide)
    (by rw [u1.other _ (by decide), hin.r0]) fun t2 h2 g2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t3 u3 => ?_
  refine (h2.upd u3 (by simp)).strb hin (by omega_arith) (by rw [u3.gpr]; rfl) (by decide)
    (by rw [u3.other _ (by decide), g2, u1.other _ (by decide), hin.r0]) fun t4 h4 g4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_dp (op2_imm (encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith))) fun t6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => WP.block_nil ?_
  have h7 := ((h4.upd u5 (by simp)).upd u6 (by simp)).upd u7 (by simp)
  have r0_7 : t7.gpr .r0 = dst + BitVec.ofNat 32 2 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, dpVal, g4, u3.other _ (by decide), g2,
      u1.other _ (by decide), hin.r0]; rfl
  have r3_7 : t7.gpr .r3 = BitVec.ofNat 32 (k - tLen h - 3) := by
    rw [u7.other _ (by decide), u6.gpr, dpVal, u5.other _ (by decide), g4, u3.other _ (by decide), g2,
      u1.other _ (by decide), hin.r3]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have r2_7 : t7.gpr .r2 = 0xff := u7.gpr
  have hps : 8 ≤ k - tLen h - 3 := by omega_arith
  -- `PS`.
  have fill_ok : WP isa fill t7 fun t => Wr s0 dst src k (encList h D k) (2 + (k - tLen h - 3)) t ∧
      t.gpr .r0 = dst + BitVec.ofNat 32 (2 + (k - tLen h - 3)) := by
    refine WP.loop (M := isa) (fun (q : Nat) (t : State) => q + 1 ≤ k - tLen h - 3 ∧
        Wr s0 dst src k (encList h D k) (2 + (k - tLen h - 3 - (q + 1))) t ∧
        t.gpr .r0 = dst + BitVec.ofNat 32 (2 + (k - tLen h - 3 - (q + 1))) ∧
        t.gpr .r3 = BitVec.ofNat 32 (q + 1) ∧ t.gpr .r2 = 0xff) ?_ (k - tLen h - 3 - 1) t7
      ⟨by omega_arith, by rw [show k - tLen h - 3 - (k - tLen h - 3 - 1 + 1) = 0 by omega_arith]; exact h7,
        by rw [r0_7, show k - tLen h - 3 - (k - tLen h - 3 - 1 + 1) = 0 by omega_arith],
        by rw [r3_7, show k - tLen h - 3 - 1 + 1 = k - tLen h - 3 by omega_arith], r2_7⟩
    rintro q t ⟨hq, ht, r0, r3, r2⟩
    refine ht.strb hin (by omega_arith) (by rw [r2, encList_ps (by omega_arith)]; rfl) (by decide)
      (by rw [r0, BitVec.add_zero]) fun t1 h1 g1 => ?_
    refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
    refine wp_subs (op2_imm (by decide)) fun t3 u3 z3 => WP.block_nil ?_
    have h3 := (h1.upd u2 (by simp)).upd u3 (by simp)
    have r3' : t3.gpr .r3 - 0 = BitVec.ofNat 32 q := by
      rw [u3.gpr, u2.other _ (by decide), g1, r3, sub_one_ofNat (by omega_arith)]; simp
    have r0' : t3.gpr .r0 = dst + BitVec.ofNat 32 (2 + (k - tLen h - 3 - (q + 1)) + 1) := by
      rw [u3.other _ (by decide), u2.gpr, dpVal, g1, r0, Offset.add_ofNat_add_one]
    have ev : isa.eval .ne t3 = some (decide (0 < q)) := by
      rw [eval_ne, z3, u2.other _ (by decide), g1, r3, ne_counter (by omega_arith)]
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      refine .inl ⟨by rw [ev]; rfl, ?_, ?_⟩
      · rw [show 2 + (k - tLen h - 3) = 2 + (k - tLen h - 3 - (0 + 1)) + 1 by omega_arith]; exact h3
      · rw [r0']; congr 2; omega_arith
    · refine .inr ⟨by rw [ev]; simp [hq0], q - 1, by omega_arith, by omega_arith, ?_, ?_, ?_, ?_⟩
      · rw [show 2 + (k - tLen h - 3 - (q - 1 + 1)) = 2 + (k - tLen h - 3 - (q + 1)) + 1 by omega_arith]; exact h3
      · rw [r0']; congr 2; omega_arith
      · rw [u3.gpr, u2.other _ (by decide), g1, r3, sub_one_ofNat (by omega_arith), show q - 1 + 1 = q by omega_arith]
      · rw [u3.other _ (by decide), u2.other _ (by decide), g1, r2]
  rw [WP.seq_iff]
  refine WP.mono fill_ok fun t8 ⟨h8, r0_8⟩ => ?_
  rw [WP.seq_iff]
  -- `0x00`, the prefix, and the hash value's registers.
  unfold mid
  refine putBytes_ok hin (L := encList h D k) (b0 := 2 + (k - tLen h - 3)) (0 :: h.prefix) 0 h8 r0_8 rfl
    (by simp; omega_arith) (fun i hi => encList_mid (by simpa using hi)) (by simp; omega_arith) fun t9 h9 g9 => ?_
  refine wp_dp (op2_imm (encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith))) fun t10 u10 => ?_
  refine wp_mov (op2_imm (encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega_arith))) fun t11 u11 => WP.block_nil ?_
  have h11 := (h9.upd u10 (by simp)).upd u11 (by simp)
  have hn : 2 + (k - tLen h - 3) + (0 :: h.prefix).length = 2 + (k - tLen h - 3) + (h.prefix.length + 1) := by simp
  rw [hn] at h11
  -- The hash value.
  have dfit : (dst + BitVec.ofNat 32 (2 + (k - tLen h - 3) + (h.prefix.length + 1))).toNat + h.len ≤ 2 ^ 32 := by
    have := hin.dstFit
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  have hk32 : k < 2 ^ 32 := by omega_arith
  have dA : ∀ j < k, State.addr (dst + BitVec.ofNat 32 j) = State.addr dst + BitVec.ofNat 64 j := fun j hj =>
    addr_add (by have := hin.dstFit; omega_arith)
  have r0_11 : t11.gpr .r0 = dst + BitVec.ofNat 32 (2 + (k - tLen h - 3) + (h.prefix.length + 1)) := by
    rw [u11.other _ (by decide), u10.gpr, dpVal, g9 _ (by decide), r0_8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdst' : State.addr (dst + BitVec.ofNat 32 (2 + (k - tLen h - 3) + (h.prefix.length + 1))) =
      State.addr dst + BitVec.ofNat 64 (2 + (k - tLen h - 3) + (h.prefix.length + 1)) := dA _ (by omega_arith)
  have sub : Region.Sub ⟨State.addr (dst + BitVec.ofNat 32 (2 + (k - tLen h - 3) + (h.prefix.length + 1))), h.len⟩
      ⟨State.addr dst, k⟩ := by
    rw [hdst']; exact Offset.sub_base _ (by omega_arith)
  have ctx := Bignum.Arm.copyCtx_of_regions t11 src (dst + BitVec.ofNat 32 (2 + (k - tLen h - 3) + (h.prefix.length + 1)))
    (n := h.len) (by omega_arith) (by rw [← hD]; exact hin.srcFit) dfit
    (by rw [h11.rest.rd, h11.rest.wr, ← hD]; exact hin.read)
    (by rw [h11.rest.wr, hdst']
        exact Covers.one hin.write _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by have := hin.sep; rw [hD] at this; exact this.sub_right sub)
  rw [WP.seq_iff]
  refine WP.mono (Bignum.Arm.copyBytes_ok t11 ctx hhp h11.r1 r0_11 u11.gpr) fun t12 h12 => ?_
  refine wp_mov (op2_imm (by decide)) fun t13 u13 => WP.block_nil ⟨?_, ?_, ?_, u13.gpr⟩
  · rw [u13.mem]
    refine h11.frame.trans fun x hx => h12.outside x fun j hj e => hx _ (List.mem_singleton_self _) ?_
    rw [e, BitVec.add_assoc, BitVec.ofNat_add_ofNat, dA _ (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · exact (h11.rest.trans (h12.rest.mono (by simp))).trans (u13.rest (by simp))
  · intro i hi
    rw [u13.mem]
    rcases (by omega_arith : i < 2 + (k - tLen h - 3) + (h.prefix.length + 1) ∨
        2 + (k - tLen h - 3) + (h.prefix.length + 1) ≤ i) with hi' | hi'
    · rw [h12.outside _ fun j hj e => ?_]
      · exact h11.bytes i hi'
      · rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, dA _ (by omega_arith)] at e
        exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith) e
    · obtain ⟨j, rfl⟩ : ∃ j, i = 2 + (k - tLen h - 3) + (h.prefix.length + 1) + j := ⟨_, (Nat.add_sub_cancel' hi').symm⟩
      have hj : j < h.len := by omega_arith
      have e1 := h12.copied j hj
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, dA _ (by omega_arith)] at e1
      rw [e1, encList_D, ← hDdef, bytesAt_getD (by omega_arith), addr_add (by have := hin.srcFit; omega_arith)]
      have sep : Region.Disjoint ⟨State.addr src + BitVec.ofNat 64 j, 1⟩ ⟨State.addr dst, k⟩ :=
        hin.sep.sub_left (Offset.sub_base _ (by omega_arith))
      exact h11.frame.byte1 fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sep

/-- The top bit of `k - x`: 1 exactly when `k < x`. -/
theorem top_sub {k x : Nat} (hk : k < 2 ^ 31) (hx : x < 2 ^ 31) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 x) >>> 31 = if k < x then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := x) (by omega)]
  by_cases h : k < x
  · simp only [h, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]
    show _ = 1
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · simp only [h, ↓reduceIte]
    rw [show 2 ^ 32 - x + k = (k - x) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    show _ = 0
    exact Nat.div_eq_of_lt (by omega)

theorem cmp_eq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr ?_, decide_eq_false h]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    have z : (0 : BitVec 32).toNat = 0 := rfl
    rw [z] at this
    omega

theorem fail_post {s : State}
    (hn : encOut id.toNat (Spec.Rsa.bytesAt s.mem (State.addr src) dl) k = none) {t : State}
    (ht : t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t ∧ t.gpr .r3 = 0) : EncPost s dst src id k dl t := by
  refine ⟨by rw [ht.1]; exact Frame.refl _ _, ht.2.1, ?_⟩
  rw [hn]; exact ht.2.2

/-- `encodeH h` for the hash function the number names. -/
theorem encodeH_ok {h : Hash} {s : State} (hin : EncIn s dst src id k dl) (hh : Hash.ofId id.toNat = some h) :
    WP isa (encodeH h) s (EncPost s dst src id k dl) := by
  have hk1 := hin.k1024
  have hhl := len_le h
  have hpl := prefix_le h
  have he : encOut id.toNat (Spec.Rsa.bytesAt s.mem (State.addr src) dl) k =
      Spec.RsaPkcs1Sig.encode h (Spec.Rsa.bytesAt s.mem (State.addr src) dl) k := by simp only [encOut, hh]
  unfold encodeH
  rw [WP.seq_iff]
  refine wp_cmp (op2_imm (encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega))) fun t1 u1 z1 => WP.block_nil ?_
  refine WP.ite _ (by rw [eval_ne]) (fun hb => ?_) (fun hb => ?_)
  · have hne : dl ≠ h.len := by
      rw [z1, hin.lr, cmp_eq hin.dl32 (by omega)] at hb; simpa using hb
    refine WP.mono fail_ok fun t ht => fail_post ?_ ⟨by rw [ht.1, u1.mem], (u1.rest _).trans ht.2.1, ht.2.2⟩
    rw [he, encode_eq, bytesAt_length]; simp [hne]
  · have heq : dl = h.len := by
      rw [z1, hin.lr, cmp_eq hin.dl32 (by omega)] at hb; simpa using hb
    rw [WP.seq_iff]
    refine wp_dp (op2_imm (encodable_of_lt (by rw [BitVec.toNat_ofNat]; simp only [tLen]; omega))) fun t2 u2 => ?_
    refine wp_mov (op2_lsr (by decide)) fun t3 u3 => ?_
    refine wp_cmp (op2_imm (by decide)) fun t4 u4 z4 => WP.block_nil ?_
    have r2 : t3.gpr .r2 = if k < tLen h + 11 then 1 else 0 := by
      rw [u3.gpr, u2.gpr, dpVal, u1.gpr, hin.r3]
      exact top_sub (by omega) (by simp only [tLen]; omega)
    refine WP.ite _ (by rw [eval_ne]) (fun hb' => ?_) (fun hb' => ?_)
    · have hlt : k < tLen h + 11 := by
        rw [z4, r2] at hb'; by_contra hc; simp [hc] at hb'
      refine WP.mono fail_ok fun t ht => fail_post ?_ ⟨by rw [ht.1, u4.mem, u3.mem, u2.mem, u1.mem],
        ((((u1.rest _).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans (u4.rest _)).trans ht.2.1, ht.2.2⟩
      rw [he, encode_eq]; simp; omega
    · have hge : tLen h + 11 ≤ k := by
        rw [z4, r2] at hb'; by_contra hc; simp [show k < tLen h + 11 by omega] at hb'
      have rest := (((u1.rest (ws := [.r2]) ).trans (u2.rest (by simp))).trans (u3.rest (by simp))).trans (u4.rest _)
      have mm : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
      have hin4 : EncIn t4 dst src (t4.gpr .r2) k dl :=
        ⟨by rw [rest.gpr _ (by decide), hin.r0], by rw [rest.gpr _ (by decide), hin.r1],
          rfl, by rw [rest.gpr _ (by decide), hin.r3], by rw [rest.gpr _ (by decide), hin.lr], hin.k64,
          hin.k1024, hin.dl32, hin.dstFit, hin.srcFit, by rw [rest.wr]; exact hin.write,
          by rw [rest.rd, rest.wr]; exact hin.read, hin.sep⟩
      refine WP.mono (write_ok hin4 heq hge) fun t ⟨fr, rt, hby, r3⟩ => ⟨by rw [← mm]; exact fr,
        (rest.mono (by simp)).trans rt, ?_⟩
      rw [he, encode_eq, bytesAt_length]
      simp only [heq, hge, and_self, ↓reduceIte]
      refine ⟨r3, ?_⟩
      rw [mm] at hby
      have hl := encList_length (h := h) (D := Spec.Rsa.bytesAt s.mem (State.addr src) dl) (k := k)
        (by rw [bytesAt_length, heq]) hge
      have := bytesAt_eq (m := t.mem) (p := State.addr dst) fun i hi => by rw [hl] at hi; exact hby i hi
      rw [hl] at this
      rw [← heq]; exact this

theorem ofId_hashes : ∀ i < 12, Hash.ofId i = hashes[i]? := by decide

theorem ofId_ge (j : Nat) : Hash.ofId (j + 12) = none := rfl

theorem EncIn.fupd {s t : State} (hin : EncIn s dst src id k dl) (u : Proof.X25519.Arm.Fupd s t) :
    EncIn t dst src id k dl :=
  ⟨by rw [u.gpr]; exact hin.r0, by rw [u.gpr]; exact hin.r1, by rw [u.gpr]; exact hin.r2,
    by rw [u.gpr]; exact hin.r3, by rw [u.gpr]; exact hin.lr, hin.k64, hin.k1024, hin.dl32, hin.dstFit,
    hin.srcFit, by rw [u.wr]; exact hin.write, by rw [u.rd, u.wr]; exact hin.read, hin.sep⟩

theorem EncPost.fupd {s t u : State} (f : Proof.X25519.Arm.Fupd s t) (h : EncPost t dst src id k dl u) :
    EncPost s dst src id k dl u := by
  obtain ⟨fr, rt, r⟩ := h
  refine ⟨by rw [← f.mem]; exact fr, (f.rest _).trans rt, ?_⟩
  rw [← f.mem]; exact r

/-- `dispatch hs i`, with `hs` the hash functions from the number `i` on. -/
theorem dispatch_ok {s : State} (hin : EncIn s dst src id k dl) :
    ∀ (hs : List Hash) (i : Nat), hashes.drop i = hs → i ≤ id.toNat →
      WP isa (dispatch hs i) s (EncPost s dst src id k dl)
  | [], i, hd, hi => by
    have h12 : 12 ≤ i := by
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at this
      exact Nat.le_of_sub_eq_zero this
    have hn : Hash.ofId id.toNat = none := by
      rw [show id.toNat = (id.toNat - 12) + 12 by omega]; exact ofId_ge _
    unfold dispatch
    exact WP.mono fail_ok fun t ht => fail_post (by simp only [encOut, hn]) ht
  | h :: hs, i, hd, hi => by
    have h12 : i < 12 := by
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at this
      have : hashes.length = 12 := rfl
      omega
    unfold dispatch
    rw [WP.seq_iff]
    refine wp_cmp (op2_imm (encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega))) fun t1 u1 z1 => WP.block_nil ?_
    have hin1 := hin.fupd u1
    have hid : id = BitVec.ofNat 32 id.toNat := by simp
    refine WP.ite _ (eval_eq _) (fun hb => ?_) (fun hb => ?_)
    · have he : id.toNat = i := by
        rw [z1, hin.r2, hid, cmp_eq id.isLt (by omega)] at hb; simpa using hb
      have hh : Hash.ofId id.toNat = some h := by
        rw [he, ofId_hashes i h12, ← Nat.add_zero i, ← List.getElem?_drop, hd]; rfl
      exact WP.mono (encodeH_ok hin1 hh) fun t ht => ht.fupd u1
    · have he : id.toNat ≠ i := by
        rw [z1, hin.r2, hid, cmp_eq id.isLt (by omega)] at hb; simpa using hb
      refine WP.mono (dispatch_ok hin1 hs (i + 1) ?_ (by omega)) fun t ht => ht.fupd u1
      rw [← List.drop_drop, hd]; rfl

/-- EMSA-PKCS1-v1_5-ENCODE to the buffer. -/
theorem encode_ok {s : State} (hin : EncIn s dst src id k dl) :
    WP isa encode s (EncPost s dst src id k dl) :=
  dispatch_ok hin hashes 0 rfl (Nat.zero_le _)

end

end VG.Proof.RsaPkcs1Sig.Arm
