module

public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCopy
import VerifiedGarbage.Proof.Dsa.Arm.Session
import VerifiedGarbage.Proof.Dsa.Arm.Body
import VerifiedGarbage.Proof.Dsa.Arm.Env
import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.Arm.Install
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps

/-!
# Writing a derived key (32-bit ARM)

`writeKey_ok`: `Generate.writeKey` copies p||q||g, y (from the working
space) and x to the output, each byte under the flag, and returns the flag's
low bit: the key if every check passed, zeros otherwise.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm.Dyn VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw op2_reg)
open VG.Proof.Ecdsa.Arm (mask32)

theorem masked_mask32 (acc : Prop) [Decidable acc] (b : Byte) : masked (mask32 acc) b = if acc then b else 0 := by
  unfold mask32 masked
  by_cases h : acc
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]; exact VG.Proof.Dsa.byte_setWidth b
  · simp [h]

theorem map_masked_mask32 (acc : Prop) [Decidable acc] (xs : List Byte) :
    xs.map (masked (mask32 acc)) = if acc then xs else List.replicate xs.length 0 := by
  rw [show masked (mask32 acc) = fun b => if acc then b else 0 from funext (masked_mask32 acc)]
  by_cases h : acc
  · simp [h]
  · simp only [h, ↓reduceIte, List.map_const']

/-- A part of a writable range, apart from a source. -/
theorem copyDst_of {s : State} {src O : BitVec 32} {L a n : Nat} (fit : O.toNat + L ≤ 2 ^ 32)
    (wr : ∀ i < L, InRegions s.wr (State.addr O + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr O, L⟩) (h : a + n ≤ L) (hn : 0 < n) :
    CopyDst s src (O + BitVec.ofNat 32 a) n := by
  have e : State.addr (O + BitVec.ofNat 32 a) = State.addr O + BitVec.ofNat 64 a := VG.Arm.addr_add (by omega)
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [e, Offset.add_add]; exact wr _ (by omega)
  · rw [e]; exact hd.sub_right (Offset.sub_base _ h)

/-- The bytes of a computed value. -/
theorem bytesIn_local {s : State} {base : Addr} {size o len : Nat} (hs : Ws s base size) (h : o + len ≤ size)
    (ho : o < size) :
    BytesIn s (pointerValue base s (.local o)) (Spec.Rsa.bytesAt s.mem (off base o) len) := by
  have nw := hs.nowrap
  have A := local_addr hs ho
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [pointerValue, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (a := o) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
    rw [A, off, Offset.add_add]; exact hs.read (by omega)
  · simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [A]

theorem BytesIn.outside {s t : State} {p O : BitVec 32} {bs : List Byte} {L : Nat} (h : BytesIn s p bs)
    (Ot : Outside (State.addr O) 0 L s.mem t.mem) (hd : Region.Disjoint ⟨State.addr p, bs.length⟩ ⟨State.addr O, L⟩)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : BytesIn t p bs := by
  refine ⟨h.fit, fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => ?_⟩
  rw [← h.val i hi]
  refine Ot _ (.inr ?_)
  rw [Nat.zero_add]
  refine ofs_apart hd.symm ?_
  have := ofs_off (State.addr p) (d := 0) (i := i) (by have := h.fit; omega)
  rw [off, BitVec.add_zero, Nat.zero_add] at this
  rw [this]; exact hi

/-- A part of a range that alone changed. -/
theorem Outside.widen {P : Addr} {e l L : Nat} {m m' : Mem} (O : Outside (P + BitVec.ofNat 64 e) 0 l m m')
    (he : e + l ≤ L) (hL : L ≤ 2 ^ 64) : Outside P 0 L m m' := fun x hx => O x (.inr (by
  have H := Offset.lt_iff x P (d := e) (n := l) (by omega)
  have : ¬ (x - (P + BitVec.ofNat 64 e)).toNat < l := fun h => by have := H.mp h; simp only [ofs] at hx; omega
  simp only [ofs]
  omega))

theorem copyFrom_ok {s : State} {src dst mask : BitVec 32} {bs : List Byte} {len : Nat}
    (r1 : s.gpr .r1 = src) (hin : BytesIn s src bs) (hlen : bs.length = len)
    (hn : len < 2 ^ 16) (h0 : 0 < len) (D : CopyDst s src dst len) (r10 : s.gpr .r10 = dst)
    (r3 : s.gpr .r3 = mask) :
    WP isa (Generate.copyFrom len) s fun u =>
      u.gpr .r10 = dst + BitVec.ofNat 32 len ∧ u.gpr .r3 = mask ∧
      Spec.Rsa.bytesAt u.mem (State.addr dst) len = bs.map (masked mask) ∧
      Outside (State.addr dst) 0 len s.mem u.mem ∧ Rest [.r0, .r1, .r2, .r10] s u := by
  subst hlen
  unfold Generate.copyFrom
  refine WP.seq (wp_movw fun t u => WP.block_nil ?_)
  have hin' : BytesIn t src bs := hin.congr u.mem u.rd u.wr
  have D' : CopyDst t src dst bs.length := ⟨D.fit, fun i hi => by rw [u.wr]; exact D.wr i hi, D.apart⟩
  refine WP.mono (copyMasked_ok hin' D' hn h0 ⟨by rw [u.other _ (by decide), r1, BitVec.add_zero],
    by rw [u.other _ (by decide), r10, BitVec.add_zero], by rw [u.gpr, movw_ofNat hn, Nat.sub_zero],
    by rw [u.other _ (by decide), r3], fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _,
    Rest.refl _ _⟩) fun v I => ⟨I.r10, I.r3, I.bytesAt, by rw [← u.mem]; exact I.out, ?_⟩
  exact (u.rest (by decide)).trans I.rest

/-- Where the key goes, and what it is copied from. -/
structure KeySources (s : State) (base : Addr) (size pLen qLen : Nat) (pb xb : List Byte) : Prop where
  ws : Ws s base size
  big : 15712 < size
  pLen16 : 3 * pLen + 2 * qLen < 2 ^ 16
  q0 : 0 < qLen
  p0 : 0 < pLen
  pl : pb.length = 2 * pLen + qLen
  xl : xb.length = qLen
  bp : BytesIn s (pointerValue base s (.input .p)) pb
  bx : BytesIn s (pointerValue base s (.input .nonce)) xb
  fit : (pointerValue base s (.input .out)).toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32
  wr : ∀ i < 3 * pLen + 2 * qLen,
    InRegions s.wr (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 i) 1
  dp : Region.Disjoint ⟨State.addr (pointerValue base s (.input .p)), 2 * pLen + qLen⟩
    ⟨State.addr (pointerValue base s (.input .out)), 3 * pLen + 2 * qLen⟩
  dx : Region.Disjoint ⟨State.addr (pointerValue base s (.input .nonce)), qLen⟩
    ⟨State.addr (pointerValue base s (.input .out)), 3 * pLen + 2 * qLen⟩
  ds : Region.Disjoint ⟨base, size⟩ ⟨State.addr (pointerValue base s (.input .out)), 3 * pLen + 2 * qLen⟩

theorem writeKey_ok {s : State} {base : Addr} {size pLen qLen : Nat} {pb xb : List Byte}
    (K : KeySources s base size pLen qLen pb xb) (acc : Prop) [Decidable acc] (hm : maskW base s = mask32 acc)
    (ht2 : Impl.Dsa.Layout.t2 + pLen ≤ size) :
    WP isa (Generate.writeKey pLen qLen) s fun u =>
      u.gpr .r0 = (if acc then 1 else 0) ∧
      Spec.Rsa.bytesAt u.mem (State.addr (pointerValue base s (.input .out))) (3 * pLen + 2 * qLen) =
        (if acc then pb ++ Spec.Rsa.bytesAt s.mem (off base Impl.Dsa.Layout.t2) pLen ++ xb
          else List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Outside (State.addr (pointerValue base s (.input .out))) 0 (3 * pLen + 2 * qLen) s.mem u.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r10, .r11] s u := by
  have hs := K.ws
  have nw := hs.nowrap
  have big := K.big
  have hb16 := K.pLen16
  have q0 := K.q0
  have p0 := K.p0
  have Lt2 : Impl.Dsa.Layout.t2 = 15328 := rfl
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  have fo : Impl.Dsa.Arm.Layout.field .out = 96 := rfl
  have fp : Impl.Dsa.Arm.Layout.field .p = 64 := rfl
  have fn : Impl.Dsa.Arm.Layout.field .nonce = 88 := rfl
  obtain ⟨O, hO⟩ : ∃ O, pointerValue base s (.input .out) = O := ⟨_, rfl⟩
  have ofit := K.fit
  have kwr := K.wr
  have kdp := K.dp
  have kdx := K.dx
  have kds := K.ds
  rw [hO] at ofit kwr kdp kdx kds ⊢
  obtain ⟨L, hL⟩ : ∃ L, 3 * pLen + 2 * qLen = L := ⟨_, rfl⟩
  rw [hL] at ofit kwr kdp kdx kds hb16 ⊢
  simp only [Generate.writeKey, Core.sequence, List.foldr]
  -- The mask and the output's pointer.
  have H : WP isa (.block [.ldr .r3 .r12 (Layout.field .mask), .ldr .r10 .r12 (Layout.field .out),
      .ldr .r1 .r12 (Layout.field .p), .ldr .r4 .r12 (Layout.field .nonce)]) s
      fun t => t.gpr .r3 = mask32 acc ∧ t.gpr .r10 = O ∧ t.mem = s.mem ∧ Rest [.r1, .r3, .r4, .r10] s t ∧
        t.gpr .r1 = pointerValue base s (.input .p) ∧ t.gpr .r4 = pointerValue base s (.input .nonce) :=
    VG.Proof.X25519.Arm.wp_ldr (by decide) (hs.ea12 (by omega)) (hs.read (by omega)) fun t₁ u₁ =>
      VG.Proof.X25519.Arm.wp_ldr (by decide) ((hs.of_upd u₁ (by decide)).ea12 (by omega))
        ((hs.of_upd u₁ (by decide)).read (by omega)) fun t₂ u₂ =>
      VG.Proof.X25519.Arm.wp_ldr (by decide) (((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).ea12 (by omega))
        (((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).read (by omega)) fun t₃ u₃ =>
      VG.Proof.X25519.Arm.wp_ldr (by decide)
        ((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).ea12 (by omega))
        ((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).read (by omega)) fun t₄ u₄ =>
      WP.block_nil
          ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, fm]; exact hm,
            by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, fo]; exact hO,
            by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
            (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
              (u₄.rest (by decide)))),
            by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]; rfl,
            by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]; rfl⟩
  refine WP.seq (WP.mono H fun t₂ ⟨m₂, o₂, M₂, R₂, p₂, x₂⟩ => ?_)
  have w₂ := hs.of_rest R₂ (by decide)
  have eA : ∀ a, a < L → State.addr (O + BitVec.ofNat 32 a) = State.addr O + BitVec.ofNat 64 a :=
    fun a ha => VG.Arm.addr_add (by omega)
  have Owr : ∀ (t : State), t.wr = s.wr → ∀ i < L, InRegions t.wr (State.addr O + BitVec.ofNat 64 i) 1 :=
    fun t ht i hi => by rw [ht]; exact kwr i hi
  -- What the copies keep: the working space, and the caller's other buffers.
  have keepW : ∀ {m : Mem}, Outside (State.addr O) 0 L s.mem m → ∀ d, d + 4 ≤ size →
      m.readW (off base d) 32 = s.mem.readW (off base d) 32 := fun Om d hd =>
    readW_apart Om (kds.sub_left (Offset.sub_base base (by omega))) (by omega) (by omega)
  -- p||q||g
  have Bp : BytesIn t₂ (pointerValue base s (.input .p)) pb := K.bp.congr M₂ R₂.rd R₂.wr
  have D₁ := copyDst_of (s := t₂) (src := pointerValue base s (.input .p)) (a := 0) ofit
    (Owr t₂ R₂.wr) kdp (by omega) (by omega)
  rw [BitVec.add_zero] at D₁
  refine WP.seq (WP.mono (copyFrom_ok p₂ Bp K.pl (by omega) (by omega) D₁ o₂ m₂)
    fun t₃ ⟨r10₃, r3₃, B₃, O₃, R₃⟩ => ?_)
  have w₃ := w₂.of_rest R₃ (by decide)
  rw [M₂] at O₃
  have O₃' : Outside (State.addr O) 0 L s.mem t₃.mem := O₃.mono (by omega) (by omega)
  -- y
  have hy : Spec.Rsa.bytesAt t₃.mem (off base Impl.Dsa.Layout.t2) pLen =
      Spec.Rsa.bytesAt s.mem (off base Impl.Dsa.Layout.t2) pLen :=
    bytes_keep O₃' (kds.sub_left (Offset.sub_base base ht2)) (by omega) (by omega)
  have By := bytesIn_local w₃ (o := Impl.Dsa.Layout.t2) (len := pLen) ht2 (by omega)
  have LA := local_addr w₃ (o := Impl.Dsa.Layout.t2) (by omega)
  have D₂ := copyDst_of (s := t₃) (src := pointerValue base t₃ (.local Impl.Dsa.Layout.t2)) (a := 2 * pLen + qLen)
    (n := pLen) ofit (Owr t₃ (R₃.wr.trans R₂.wr))
    (by rw [LA]; exact kds.sub_left (Offset.sub_base base ht2)) (by omega) p0
  refine WP.seq (wp_ptr (is := []) (by decide) (show Impl.Dsa.Layout.t2 < 2 ^ 16 by decide) fun t₃' u₃' =>
    WP.block_nil ?_)
  refine WP.seq (WP.mono (copyFrom_ok (mask := mask32 acc) (dst := O + BitVec.ofNat 32 (2 * pLen + qLen)) u₃'.gpr (By.congr u₃'.mem u₃'.rd u₃'.wr) (by simp [Spec.Rsa.bytesAt])
    (by omega) p0 ⟨D₂.fit, fun i hi => by rw [u₃'.wr]; exact D₂.wr i hi, D₂.apart⟩
    (by rw [u₃'.other _ (by decide), r10₃]) (by rw [u₃'.other _ (by decide), r3₃]))
    fun t₄ ⟨r10₄, r3₄, B₄, O₄, R₄⟩ => ?_)
  rw [u₃'.mem] at O₄
  have w₄ := (w₃.of_upd u₃' (by decide)).of_rest R₄ (by decide)
  rw [eA _ (by omega)] at O₄ B₄
  have O₄' : Outside (State.addr O) 0 L s.mem t₄.mem := O₃'.trans (Outside.widen O₄ (by omega) (by omega))
  -- x
  have Bx : BytesIn t₄ (pointerValue base s (.input .nonce)) xb :=
    K.bx.outside O₄' (by rw [K.xl]; exact kdx) (by rw [R₄.rd, u₃'.rd, R₃.rd, R₂.rd]) (by rw [R₄.wr, u₃'.wr, R₃.wr, R₂.wr])
  have D₃ := copyDst_of (s := t₄) (src := pointerValue base s (.input .nonce)) (a := 2 * pLen + qLen + pLen)
    (n := qLen) ofit (Owr t₄ (R₄.wr.trans (u₃'.wr.trans (R₃.wr.trans R₂.wr)))) kdx (by omega) q0
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat] at r10₄
  have r4₄ : t₄.gpr .r4 = pointerValue base s (.input .nonce) := by
    rw [R₄.gpr _ (by decide), u₃'.other _ (by decide), R₃.gpr _ (by decide), x₂]
  refine WP.seq (wp_mov (op2_reg _ _) fun t₄' u₄' => WP.block_nil ?_)
  refine WP.seq (WP.mono (copyFrom_ok (mask := mask32 acc) (src := pointerValue base s (.input .nonce))
    (dst := O + BitVec.ofNat 32 (2 * pLen + qLen + pLen)) (by rw [u₄'.gpr, r4₄]) (Bx.congr u₄'.mem u₄'.rd u₄'.wr) K.xl (by omega) q0
    ⟨D₃.fit, fun i hi => by rw [u₄'.wr]; exact D₃.wr i hi, D₃.apart⟩ (by rw [u₄'.other _ (by decide), r10₄])
    (by rw [u₄'.other _ (by decide), r3₄])) fun t₅ ⟨_, r3₅, B₅, O₅, R₅⟩ => ?_)
  rw [u₄'.mem] at O₅
  have w₅ := (w₄.of_upd u₄' (by decide)).of_rest R₅ (by decide)
  rw [eA _ (by omega)] at O₅ B₅
  have O₅' : Outside (State.addr O) 0 L s.mem t₅.mem := O₄'.trans (Outside.widen O₅ (by omega) (by omega))
  -- The result.
  have hm₅ : maskW base t₅ = mask32 acc := by
    rw [← hm]; exact keepW O₅' 116 (by omega)
  refine WP.seq (WP.mono (result_ok w₅ (by omega) acc hm₅) fun u ⟨r0, Ru, Mu⟩ => WP.block_nil ?_)
  refine ⟨r0, ?_, by rw [Mu]; exact O₅', ?_⟩
  · -- The three parts.
    have k₅ : ∀ {a n : Nat}, a + n ≤ 2 * pLen + qLen + pLen →
        Spec.Rsa.bytesAt u.mem (State.addr O + BitVec.ofNat 64 a) n =
          Spec.Rsa.bytesAt t₄.mem (State.addr O + BitVec.ofNat 64 a) n := fun h => by
      rw [Mu]; exact bytes_keep O₅ (Offset.disjoint _ (.inl h) (by omega) (by omega)) (by omega) (by omega)
    have k₄ : ∀ {n : Nat}, n ≤ 2 * pLen + qLen →
        Spec.Rsa.bytesAt t₄.mem (State.addr O) n = Spec.Rsa.bytesAt t₃.mem (State.addr O) n := fun h => by
      exact bytes_keep O₄ (Offset.base_disjoint _ h (by omega)) (by omega) (by omega)
    have P1 : Spec.Rsa.bytesAt u.mem (State.addr O) (2 * pLen + qLen) = pb.map (masked (mask32 acc)) := by
      have := k₅ (a := 0) (n := 2 * pLen + qLen) (by omega)
      rw [BitVec.add_zero] at this
      rw [this, k₄ (Nat.le_refl _), B₃]
    have P2 : Spec.Rsa.bytesAt u.mem (State.addr O + BitVec.ofNat 64 (2 * pLen + qLen)) pLen =
        (Spec.Rsa.bytesAt s.mem (off base Impl.Dsa.Layout.t2) pLen).map (masked (mask32 acc)) := by
      rw [k₅ (by omega), B₄, hy]
    have P3 : Spec.Rsa.bytesAt u.mem (State.addr O + BitVec.ofNat 64 (2 * pLen + qLen + pLen)) qLen =
        xb.map (masked (mask32 acc)) := by
      rw [Mu, B₅]
    rw [← hL, show 3 * pLen + 2 * qLen = (2 * pLen + qLen) + pLen + qLen by omega, VG.Proof.Dsa.bytesAt_split,
      VG.Proof.Dsa.bytesAt_split, P1, P2, P3, ← List.map_append, ← List.map_append, map_masked_mask32]
    split
    · rfl
    · simp only [List.length_append, K.pl, K.xl, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · exact ((((((R₂.mono (by decide)).trans (R₃.mono (by decide))).trans (u₃'.rest (by decide))).trans
      (R₄.mono (by decide))).trans (u₄'.rest (by decide))).trans (R₅.mono (by decide))).trans (Ru.mono (by decide))

end VG.Proof.Dsa.Arm
