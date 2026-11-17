module

public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFrame
import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.PublicKey
import VerifiedGarbage.Proof.Dsa.Arm.Body
import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Dsa.OutputBytes
public import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Zeroize.Common
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateCompute
import Mathlib.Basic.Logic.Basic
import Mathlib.Logic.Function.Basic

/-! ### `Dsa.Arm.GenerateWrite`, which only this module used -/

section

/-! ### `Dsa.Arm.GenerateCopy`, which only this module used -/

section

/-!
# Copying bytes under a mask (32-bit ARM)

`copyMasked_ok`: `Generate.copyMasked` copies `n > 0` bytes from `r1` to
`r10`, each and-ed with the mask in `r3`, leaving `r10` past them; it writes
only those bytes.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_dp wp_ldrb wp_strb op2_reg eval_ne ofNat_beq_zero dpVal)

/-- A byte under a mask. -/
abbrev masked (mask : BitVec 32) (b : Byte) : Byte := (b.setWidth 32 &&& mask).setWidth 8

/-- The copy after its first `k` bytes. -/
structure CopyMaskInv (s : State) (src dst : BitVec 32) (bs : List Byte) (mask : BitVec 32) (k : Nat)
    (t : State) : Prop where
  r1 : t.gpr .r1 = src + BitVec.ofNat 32 k
  r10 : t.gpr .r10 = dst + BitVec.ofNat 32 k
  r2 : t.gpr .r2 = BitVec.ofNat 32 (bs.length - k)
  r3 : t.gpr .r3 = mask
  bytes : ∀ i < k, t.mem (State.addr dst + BitVec.ofNat 64 i) = masked mask (bs.getD i 0)
  out : Outside (State.addr dst) 0 bs.length s.mem t.mem
  rest : Rest [.r0, .r1, .r2, .r10] s t

/-- Where the copy goes: writable bytes below `2³²`, apart from the source. -/
structure CopyDst (s : State) (src dst : BitVec 32) (n : Nat) : Prop where
  fit : dst.toNat + n ≤ 2 ^ 32
  wr : ∀ i < n, InRegions s.wr (State.addr dst + BitVec.ofNat 64 i) 1
  apart : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩

theorem copyStep_ok {s t : State} {src dst : BitVec 32} {bs : List Byte} {mask : BitVec 32} {k : Nat}
    (hin : BytesIn s src bs) (D : CopyDst s src dst bs.length) (hn : bs.length < 2 ^ 16) (hk : k < bs.length)
    (I : CopyMaskInv s src dst bs mask k t) :
    WP isa (.block Generate.copyStep) t fun u => CopyMaskInv s src dst bs mask (k + 1) u ∧
      u.z = decide (bs.length - (k + 1) = 0) := by
  have hfit := hin.fit
  have dfit := D.fit
  obtain hlt : bs.length < 2 ^ 32 := by omega_using [hn]
  -- The source byte, apart from what the copy wrote.
  obtain src_ofs : ofs (State.addr src) (State.addr src + BitVec.ofNat 64 k) = k := by
    have := ofs_off (State.addr src) (d := 0) (i := k) (by omega_using [hn, hk])
    rwa [off, BitVec.add_zero, Nat.zero_add] at this
  obtain keep : t.mem (State.addr src + BitVec.ofNat 64 k) = bs[k] := by
    rw [I.out _ (.inr (by rw [Nat.zero_add]; exact ofs_apart D.apart.symm (by omega_using [hk, src_ofs]))), hin.val k hk]
  unfold Generate.copyStep
  refine wp_ldrb (a := State.addr src + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega_using [hk, hfit])])
    (by rw [I.rest.rd, I.rest.wr]; exact hin.rd k hk) fun t₁ u₁ => ?_
  rw [keep] at u₁
  refine wp_dp (op2_reg _ _) fun t₂ u₂ => ?_
  refine wp_strb (a := State.addr dst + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, u₂.other _ (by decide), u₁.other _ (by decide), I.r10, VG.Arm.addr_add (by omega_using [hk, dfit])])
    (by rw [u₂.wr, u₁.wr, I.rest.wr]; exact D.wr k hk) fun t₃ u₃ => ?_
  refine wp_inc fun t₄ u₄ => wp_inc fun t₅ u₅ => wp_dec fun t₆ u₆ z₆ => WP.block_nil ?_
  obtain r3 : t₂.gpr .r3 = mask := by rw [u₂.other _ (by decide), u₁.other _ (by decide), I.r3]
  obtain v₂ : t₂.gpr .r0 = (bs[k]).setWidth 32 &&& mask := by
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other _ (by decide), I.r3]
  obtain m₆ : t₆.mem = t.mem.writeW (State.addr dst + BitVec.ofNat 64 k) (masked mask bs[k]) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v₂, u₂.mem, u₁.mem]
  obtain R : Rest [.r0, .r1, .r2, .r10] t t₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest _).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  obtain r2 : t₆.gpr .r2 = BitVec.ofNat 32 (bs.length - (k + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega_using [hk]), show bs.length - k - 1 = bs.length - (k + 1) by omega_using []]
  obtain dst_ofs : ∀ i, i < bs.length →
      ofs (State.addr dst) (State.addr dst + BitVec.ofNat 64 i) = i := fun i hi => by
    have := ofs_off (State.addr dst) (d := 0) (i := i) (by omega_using [hn, hi])
    rwa [off, BitVec.add_zero, Nat.zero_add] at this
  obtain O : Outside (State.addr dst) 0 bs.length t.mem t₆.mem := by
    rw [m₆]
    have := writeW8_outside t.mem (State.addr dst) (d := k) (masked mask bs[k]) (by omega_using [hn, hk])
    simp only [off] at this
    exact this.mono (by omega_using []) (by omega_using [hk])
  refine ⟨⟨?_, ?_, r2, ?_, fun i hi => ?_, I.out.trans O, I.rest.trans R⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      I.r1, Offset.add_ofNat_add_one]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), I.r10, Offset.add_ofNat_add_one]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, r3]
  · rw [m₆]
    by_cases hik : i = k
    · subst hik
      rw [writeW8_self, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    · rw [(writeW8_outside t.mem (State.addr dst) (d := k) (masked mask bs[k]) (by omega_using [hn, hk])) _
        (by rw [dst_ofs i (by omega_using [hk, hi])]; omega_using [hik])]
      exact I.bytes i (by omega_using [hi, hik])
  · rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      I.r2, ofNat_sub_one (by omega_using [hk]), show bs.length - k - 1 = bs.length - (k + 1) by omega_using [],
      ofNat_beq_zero (by omega_using [hn])]

theorem copyMasked_ok {s : State} {src dst : BitVec 32} {bs : List Byte} {mask : BitVec 32}
    (hin : BytesIn s src bs) (D : CopyDst s src dst bs.length) (hn : bs.length < 2 ^ 16) (h0 : 0 < bs.length)
    (I : CopyMaskInv s src dst bs mask 0 s) :
    WP isa Generate.copyMasked s fun u => CopyMaskInv s src dst bs mask bs.length u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) =>
      ∃ j, n = bs.length - j ∧ j < bs.length ∧ CopyMaskInv s src dst bs mask j u)
    (fun n u hu => ?_) bs.length s ⟨0, by omega_using [], h0, I⟩
  obtain ⟨j, hnj, hj, J⟩ := hu
  refine WP.mono (copyStep_ok hin D hn hj J) fun v ⟨J', z⟩ => ?_
  by_cases he : bs.length - (j + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z, decide_eq_true he]; rfl, ?_⟩
    rw [show bs.length = j + 1 by omega_using [hj, he]]; exact J'
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, bs.length - (j + 1), by omega_using [hnj, hj], j + 1, rfl, by omega_using [he], J'⟩

/-- The copied bytes. -/
theorem CopyMaskInv.bytesAt {s t : State} {src dst : BitVec 32} {bs : List Byte} {mask : BitVec 32}
    (I : CopyMaskInv s src dst bs mask bs.length t) :
    Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = bs.map (masked mask) := by
  apply List.ext_getElem
  · simp [Spec.Rsa.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [I.bytes i (by simpa [Spec.Rsa.bytesAt] using h₁), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h₂), Option.getD_some]

end VG.Proof.Dsa.Arm

end

end


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
  obtain e : State.addr (O + BitVec.ofNat 32 a) = State.addr O + BitVec.ofNat 64 a := VG.Arm.addr_add (by omega_using [fit, h, hn])
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_using [fit, h, hn]), Nat.mod_eq_of_lt (by omega_using [fit, h, hn])]
    omega_using [fit, h]
  · rw [e, Offset.add_add]; exact wr _ (by omega_using [h, hi])
  · rw [e]; exact hd.sub_right (Offset.sub_base _ h)

/-- The bytes of a computed value. -/
theorem bytesIn_local {s : State} {base : Addr} {size o len : Nat} (hs : Ws s base size) (h : o + len ≤ size)
    (ho : o < size) :
    BytesIn s (pointerValue base s (.local o)) (Spec.Rsa.bytesAt s.mem (off base o) len) := by
  have nw := hs.nowrap
  obtain A := local_addr hs ho
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [pointerValue, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, nw]),
      Nat.mod_eq_of_lt (by omega_using [ho, nw])]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega_using [h, nw]
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
    rw [A, off, Offset.add_add]; exact hs.read (by omega_using [h, hi])
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
  have := ofs_off (State.addr p) (d := 0) (i := i) (by have := h.fit; omega_using [hi, this])
  rw [off, BitVec.add_zero, Nat.zero_add] at this
  rw [this]; exact hi

/-- A part of a range that alone changed. -/
theorem Outside.widen {P : Addr} {e l L : Nat} {m m' : Mem} (O : Outside (P + BitVec.ofNat 64 e) 0 l m m')
    (he : e + l ≤ L) (hL : L ≤ 2 ^ 64) : Outside P 0 L m m' := fun x hx => O x (.inr (by
  obtain H := Offset.lt_iff x P (d := e) (n := l) (by omega_using [he, hL])
  have : ¬ (x - (P + BitVec.ofNat 64 e)).toNat < l := fun h => by have := H.mp h; simp only [ofs] at hx; omega_using [he, hx, H, h]
  simp only [ofs]
  omega_using [this]))

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
  obtain hin' : BytesIn t src bs := hin.congr u.mem u.rd u.wr
  obtain D' : CopyDst t src dst bs.length := ⟨D.fit, fun i hi => by rw [u.wr]; exact D.wr i hi, D.apart⟩
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
  obtain H : WP isa (.block [.ldr .r3 .r12 (Layout.field .mask), .ldr .r10 .r12 (Layout.field .out),
      .ldr .r1 .r12 (Layout.field .p), .ldr .r4 .r12 (Layout.field .nonce)]) s
      fun t => t.gpr .r3 = mask32 acc ∧ t.gpr .r10 = O ∧ t.mem = s.mem ∧ Rest [.r1, .r3, .r4, .r10] s t ∧
        t.gpr .r1 = pointerValue base s (.input .p) ∧ t.gpr .r4 = pointerValue base s (.input .nonce) :=
    VG.Proof.X25519.Arm.wp_ldr (by decide) (hs.ea12 (by omega_arith)) (hs.read (by omega_arith)) fun t₁ u₁ =>
      VG.Proof.X25519.Arm.wp_ldr (by decide) ((hs.of_upd u₁ (by decide)).ea12 (by omega_arith))
        ((hs.of_upd u₁ (by decide)).read (by omega_arith)) fun t₂ u₂ =>
      VG.Proof.X25519.Arm.wp_ldr (by decide) (((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).ea12 (by omega_arith))
        (((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).read (by omega_arith)) fun t₃ u₃ =>
      VG.Proof.X25519.Arm.wp_ldr (by decide)
        ((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).ea12 (by omega_arith))
        ((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).read (by omega_arith)) fun t₄ u₄ =>
      WP.block_nil
          ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, fm]; exact hm,
            by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, fo]; exact hO,
            by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
            (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
              (u₄.rest (by decide)))),
            by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]; rfl,
            by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]; rfl⟩
  refine WP.seq (WP.mono H fun t₂ ⟨m₂, o₂, M₂, R₂, p₂, x₂⟩ => ?_)
  obtain w₂ := hs.of_rest R₂ (by decide)
  obtain eA : ∀ a, a < L → State.addr (O + BitVec.ofNat 32 a) = State.addr O + BitVec.ofNat 64 a :=
    fun a ha => VG.Arm.addr_add (by omega_arith)
  obtain Owr : ∀ (t : State), t.wr = s.wr → ∀ i < L, InRegions t.wr (State.addr O + BitVec.ofNat 64 i) 1 :=
    fun t ht i hi => by rw [ht]; exact kwr i hi
  -- What the copies keep: the working space, and the caller's other buffers.
  obtain keepW : ∀ {m : Mem}, Outside (State.addr O) 0 L s.mem m → ∀ d, d + 4 ≤ size →
      m.readW (off base d) 32 = s.mem.readW (off base d) 32 := fun Om d hd =>
    readW_apart Om (kds.sub_left (Offset.sub_base base (by omega_arith))) (by omega_arith) (by omega_arith)
  -- p||q||g
  obtain Bp : BytesIn t₂ (pointerValue base s (.input .p)) pb := K.bp.congr M₂ R₂.rd R₂.wr
  obtain D₁ := copyDst_of (s := t₂) (src := pointerValue base s (.input .p)) (a := 0) ofit
    (Owr t₂ R₂.wr) kdp (by omega_arith) (by omega_arith)
  rw [BitVec.add_zero] at D₁
  refine WP.seq (WP.mono (copyFrom_ok p₂ Bp K.pl (by omega_arith) (by omega_arith) D₁ o₂ m₂)
    fun t₃ ⟨r10₃, r3₃, B₃, O₃, R₃⟩ => ?_)
  obtain w₃ := w₂.of_rest R₃ (by decide)
  rw [M₂] at O₃
  obtain O₃' : Outside (State.addr O) 0 L s.mem t₃.mem := O₃.mono (by omega_arith) (by omega_arith)
  -- y
  obtain hy : Spec.Rsa.bytesAt t₃.mem (off base Impl.Dsa.Layout.t2) pLen =
      Spec.Rsa.bytesAt s.mem (off base Impl.Dsa.Layout.t2) pLen :=
    bytes_keep O₃' (kds.sub_left (Offset.sub_base base ht2)) (by omega_arith) (by omega_arith)
  obtain By := bytesIn_local w₃ (o := Impl.Dsa.Layout.t2) (len := pLen) ht2 (by omega_arith)
  obtain LA := local_addr w₃ (o := Impl.Dsa.Layout.t2) (by omega_arith)
  obtain D₂ := copyDst_of (s := t₃) (src := pointerValue base t₃ (.local Impl.Dsa.Layout.t2)) (a := 2 * pLen + qLen)
    (n := pLen) ofit (Owr t₃ (R₃.wr.trans R₂.wr))
    (by rw [LA]; exact kds.sub_left (Offset.sub_base base ht2)) (by omega_arith) p0
  refine WP.seq (wp_ptr (is := []) (by decide) (show Impl.Dsa.Layout.t2 < 2 ^ 16 by decide) fun t₃' u₃' =>
    WP.block_nil ?_)
  refine WP.seq (WP.mono (copyFrom_ok (mask := mask32 acc) (dst := O + BitVec.ofNat 32 (2 * pLen + qLen)) u₃'.gpr (By.congr u₃'.mem u₃'.rd u₃'.wr) (by simp [Spec.Rsa.bytesAt])
    (by omega_arith) p0 ⟨D₂.fit, fun i hi => by rw [u₃'.wr]; exact D₂.wr i hi, D₂.apart⟩
    (by rw [u₃'.other _ (by decide), r10₃]) (by rw [u₃'.other _ (by decide), r3₃]))
    fun t₄ ⟨r10₄, r3₄, B₄, O₄, R₄⟩ => ?_)
  rw [u₃'.mem] at O₄
  obtain w₄ := (w₃.of_upd u₃' (by decide)).of_rest R₄ (by decide)
  rw [eA _ (by omega_arith)] at O₄ B₄
  obtain O₄' : Outside (State.addr O) 0 L s.mem t₄.mem := O₃'.trans (Outside.widen O₄ (by omega_arith) (by omega_arith))
  -- x
  obtain Bx : BytesIn t₄ (pointerValue base s (.input .nonce)) xb :=
    K.bx.outside O₄' (by rw [K.xl]; exact kdx) (by rw [R₄.rd, u₃'.rd, R₃.rd, R₂.rd]) (by rw [R₄.wr, u₃'.wr, R₃.wr, R₂.wr])
  obtain D₃ := copyDst_of (s := t₄) (src := pointerValue base s (.input .nonce)) (a := 2 * pLen + qLen + pLen)
    (n := qLen) ofit (Owr t₄ (R₄.wr.trans (u₃'.wr.trans (R₃.wr.trans R₂.wr)))) kdx (by omega_arith) q0
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat] at r10₄
  obtain r4₄ : t₄.gpr .r4 = pointerValue base s (.input .nonce) := by
    rw [R₄.gpr _ (by decide), u₃'.other _ (by decide), R₃.gpr _ (by decide), x₂]
  refine WP.seq (wp_mov (op2_reg _ _) fun t₄' u₄' => WP.block_nil ?_)
  refine WP.seq (WP.mono (copyFrom_ok (mask := mask32 acc) (src := pointerValue base s (.input .nonce))
    (dst := O + BitVec.ofNat 32 (2 * pLen + qLen + pLen)) (by rw [u₄'.gpr, r4₄]) (Bx.congr u₄'.mem u₄'.rd u₄'.wr) K.xl (by omega_arith) q0
    ⟨D₃.fit, fun i hi => by rw [u₄'.wr]; exact D₃.wr i hi, D₃.apart⟩ (by rw [u₄'.other _ (by decide), r10₄])
    (by rw [u₄'.other _ (by decide), r3₄])) fun t₅ ⟨_, r3₅, B₅, O₅, R₅⟩ => ?_)
  rw [u₄'.mem] at O₅
  obtain w₅ := (w₄.of_upd u₄' (by decide)).of_rest R₅ (by decide)
  rw [eA _ (by omega_arith)] at O₅ B₅
  obtain O₅' : Outside (State.addr O) 0 L s.mem t₅.mem := O₄'.trans (Outside.widen O₅ (by omega_arith) (by omega_arith))
  -- The result.
  obtain hm₅ : maskW base t₅ = mask32 acc := by
    rw [← hm]; exact keepW O₅' 116 (by omega_arith)
  refine WP.seq (WP.mono (result_ok w₅ (by omega_arith) acc hm₅) fun u ⟨r0, Ru, Mu⟩ => WP.block_nil ?_)
  refine ⟨r0, ?_, by rw [Mu]; exact O₅', ?_⟩
  · -- The three parts.
    obtain k₅ : ∀ {a n : Nat}, a + n ≤ 2 * pLen + qLen + pLen →
        Spec.Rsa.bytesAt u.mem (State.addr O + BitVec.ofNat 64 a) n =
          Spec.Rsa.bytesAt t₄.mem (State.addr O + BitVec.ofNat 64 a) n := fun h => by
      rw [Mu]; exact bytes_keep O₅ (Offset.disjoint _ (.inl h) (by omega_arith) (by omega_arith)) (by omega_arith) (by omega_arith)
    obtain k₄ : ∀ {n : Nat}, n ≤ 2 * pLen + qLen →
        Spec.Rsa.bytesAt t₄.mem (State.addr O) n = Spec.Rsa.bytesAt t₃.mem (State.addr O) n := fun h => by
      exact bytes_keep O₄ (Offset.base_disjoint _ h (by omega_arith)) (by omega_arith) (by omega_arith)
    obtain P1 : Spec.Rsa.bytesAt u.mem (State.addr O) (2 * pLen + qLen) = pb.map (masked (mask32 acc)) := by
      have := k₅ (a := 0) (n := 2 * pLen + qLen) (by omega_arith)
      rw [BitVec.add_zero] at this
      rw [this, k₄ (Nat.le_refl _), B₃]
    obtain P2 : Spec.Rsa.bytesAt u.mem (State.addr O + BitVec.ofNat 64 (2 * pLen + qLen)) pLen =
        (Spec.Rsa.bytesAt s.mem (off base Impl.Dsa.Layout.t2) pLen).map (masked (mask32 acc)) := by
      rw [k₅ (by omega_arith), B₄, hy]
    obtain P3 : Spec.Rsa.bytesAt u.mem (State.addr O + BitVec.ofNat 64 (2 * pLen + qLen + pLen)) qLen =
        xb.map (masked (mask32 acc)) := by
      rw [Mu, B₅]
    rw [← hL, show 3 * pLen + 2 * qLen = (2 * pLen + qLen) + pLen + qLen by omega_arith, VG.Proof.Dsa.bytesAt_split,
      VG.Proof.Dsa.bytesAt_split, P1, P2, P3, ← List.map_append, ← List.map_append, map_masked_mask32]
    split
    · rfl
    · simp only [List.length_append, K.pl, K.xl, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · exact ((((((R₂.mono (by decide)).trans (R₃.mono (by decide))).trans (u₃'.rest (by decide))).trans
      (R₄.mono (by decide))).trans (u₄'.rest (by decide))).trans (R₅.mono (by decide))).trans (Ru.mono (by decide))

end VG.Proof.Dsa.Arm

end

end


/-!
# DSA key derivation on 32-bit ARM: correctness

`derive_correct`: from `deriveArm`'s precondition, `vg_dsa_derive_key`
returns the status of `Spec.Dsa.deriveKeyBytes` and writes its key (or
zeros), and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest eval_eq wp_mov wp_movw wp_dp op2_imm op2_reg dpVal)

/-- Key derivation, by the checks the code makes. -/
theorem deriveKeyBytes_iff {pLen qLen : Nat} {params x : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen) (hxl : x.length = qLen) :
    Spec.Dsa.deriveKeyBytes pLen qLen params x =
      if shapeValid (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q ∧
          deriveChecks (Spec.Dsa.paramsBytes pLen qLen params).p (Spec.Dsa.paramsBytes pLen qLen params).q
            (Spec.Dsa.paramsBytes pLen qLen params).g (Spec.Dsa.decodeBE x)
      then some (params ++ Spec.Dsa.encodeBE pLen ((Spec.Dsa.paramsBytes pLen qLen params).g ^
        Spec.Dsa.decodeBE x % (Spec.Dsa.paramsBytes pLen qLen params).p) ++ x)
      else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq hl hpl hxl]
  simp only [VG.Proof.Dsa.powMod_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  refine if_congr ⟨fun ⟨⟨a, b, c⟩, d, e, f, g, h⟩ => ⟨⟨a, c, b⟩, ⟨⟨g, e⟩, d⟩, h, f⟩,
    fun ⟨⟨a, c, b⟩, ⟨⟨g, e⟩, d⟩, h, f⟩ => ⟨⟨a, b, c⟩, d, e, f, g, h⟩⟩ rfl rfl

/-- The derivation's failure: zeros in the output and 0 in `r0`. -/
theorem deriveFailure_ok {s : State} {base : Addr} {size pLen qLen : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (hL : 3 * pLen + 2 * qLen < 2 ^ 16) (h0 : 0 < 3 * pLen + 2 * qLen)
    (fit : (pointerValue base s (.input .out)).toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (wr : ∀ i < 3 * pLen + 2 * qLen,
      InRegions s.wr (State.addr (pointerValue base s (.input .out)) + BitVec.ofNat 64 i) 1) :
    WP isa (Generate.deriveFailure pLen qLen) s fun t =>
      t.gpr .r0 = 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s (.input .out))) (3 * pLen + 2 * qLen) =
        List.replicate (3 * pLen + 2 * qLen) 0 ∧
      Rest [.r0, .r4, .r11, .lr] s t ∧
      Outside (State.addr (pointerValue base s (.input .out))) 0 (3 * pLen + 2 * qLen) s.mem t.mem := by
  simp only [Generate.deriveFailure, Core.sequence, List.foldr]
  refine WP.seq (wp_ldr12 hs (d := 96) (by decide) (by omega_arith) fun u₁ v₁ => ?_)
  refine wp_movw fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => wp_mov (op2_imm (by decide)) fun u₄ v₄ => WP.block_nil ?_
  obtain out : u₄.gpr .r11 = pointerValue base s (.input .out) := by
    rw [v₄.other .r11 (by decide), v₃.other .r11 (by decide), v₂.other .r11 (by decide), v₁.gpr]; rfl
  obtain lr : u₄.gpr .lr = pointerValue base s (.input .out) + BitVec.ofNat 32 (3 * pLen + 2 * qLen) := by
    rw [v₄.other .lr (by decide), v₃.gpr, dpVal, v₂.gpr, v₂.other .r11 (by decide), v₁.gpr, movw_ofNat hL]
    rfl
  obtain R₄ : Rest [.r4, .r11, .lr] s u₄ :=
    (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide))).trans (v₄.rest (by decide))
  obtain M₄ : u₄.mem = s.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine WP.seq (WP.mono (failureLoop_ok h0 fit (by omega_arith) out lr v₄.gpr
    (fun i hi => by rw [R₄.wr]; exact wr i hi)) fun t ⟨B, Ot, Rt⟩ => ?_)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun t' v => WP.block_nil (WP.block_nil ⟨v.gpr, ?_, ?_, ?_⟩))
  · rw [v.mem]; exact VG.Proof.Zeroize.prefix_spec B
  · exact ((R₄.mono (by decide)).trans (Rt.mono (by decide))).trans (v.rest (by decide))
  · rw [v.mem, ← M₄]; exact Ot

/-- The derivation's inputs, at a state with its environment. -/
theorem deriveIn {s t : State} {base : Addr} {size : Nat} (h : derivePre s) (hb : State.addr (arg s 3) = base)
    (hsz : (arg s 4).toNat * 8 = size) (E : Env s base size (deriveFields s) t) :
    Input t base size (.input .p) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)) ∧
      Input t base size (.input .q) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat)
          (arg s 2).toNat)) ∧
      Input t base size (.input .g) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)) ∧
      Input t base size (.input .nonce) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, dPS, dXS, _, _, fP, fX, _, hv, _, hr3, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hz : 4960 ≤ (arg s 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain pr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  obtain xr : (⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  obtain ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (arg s 0).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r2) (by simp))
    pr fP (by omega_arith) (.inr rfl) dPS hz
  rw [BitVec.add_zero] at ip
  obtain ix := input_of E (p := .input .nonce) (by decide : Impl.Dsa.Layout.Field.nonce ≠ .mask) (o := 0)
    (len := (arg s 2).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 88) (v := arg s 1) (by simp))
    xr fX (by omega_arith) (.inr rfl) dXS hz
  rw [BitVec.add_zero] at ix
  obtain cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r2) xs).trans (congrArg (fun n => s.gpr .r2 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ pr fP (by omega_arith)
      (.inl (by omega_arith)) dPS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ pr fP (by omega_arith)
      (.inl (by omega_arith)) dPS hz, ix⟩
  · exact (E.field (d := 68) (v := s.gpr .r2 + arg s 0) (by simp)).trans (cg (xs := [arg s 0]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r2 + arg s 0 + arg s 2) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2]) (by simp))

/-- A caller's buffer apart from the working space, through the environment. -/
theorem bytesIn_env {s₀ t : State} {base : Addr} {size : Nat} {fields : Fields} (E : Env s₀ base size fields t)
    {P : BitVec 32} {n : Nat} (hr : (⟨State.addr P, n⟩ : Region) ∈ s₀.rd) (hfit : P.toNat + n ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr P, n⟩ ⟨base, size⟩) :
    BytesIn t P (Spec.Rsa.bytesAt s₀.mem (State.addr P) n) := by
  have nw := E.ws.nowrap
  refine ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hfit, fun i hi => ?_,
    fun i hi => ?_⟩
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
    rw [E.rd, E.wr]
    exact ⟨_, List.mem_append_left _ hr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    refine E.mem _ (.inr ?_)
    rw [Nat.zero_add]
    refine ofs_apart hd.symm ?_
    have := ofs_off (State.addr P) (d := 0) (i := i) (by omega_arith)
    rw [off, BitVec.add_zero, Nat.zero_add] at this
    rw [this]; exact hi

/-- The domain's components and x, as the derivation reads them. -/
abbrev deriveP (s : State) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)
abbrev deriveQ (s : State) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat)
abbrev deriveG (s : State) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
    (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)
abbrev deriveXv (s : State) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)

/-- A derivation whose computation makes the checks `C`, which for the
domain at hand are the derivation's. -/
theorem deriveWith_correct {compute : Nat → Nat → Prog isa} {C : Nat → Nat → Nat → Nat → Prop}
    [∀ P Q G X, Decidable (C P Q G X)] (hc : ComputeOk compute C) {s : State} (h : derivePre s)
    (hC : shapeValid (deriveP s) (deriveQ s) →
      (C (deriveP s) (deriveQ s) (deriveG s) (deriveXv s) ↔ deriveChecks (deriveP s) (deriveQ s) (deriveG s) (deriveXv s))) :
    WP isa (Generate.deriveWith compute) s fun t => abiPreserved s t ∧ deriveArm.post s t := by
  obtain ⟨hsp, hrd, hwr, dOP, dOX, dOS, dOA, dPS, dXS, dSA, fO, fP, fX, fS, hv, hr1, hr3, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hs16 : 128 * (arg s 0).toNat ≤ (arg s 4).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Generate.deriveWith, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (deriveEntry_ok h) fun u I => ?_)
  obtain E₀ := Env.of_installed I (by omega_arith)
  obtain fok := deriveFields_ok s
  refine WP.seq (genDispatch_ok (Generate.deriveSized compute) _ E₀.ws (by omega_arith) (genWidths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := arg s 0) (by simp)]) (by rw [E₀.field (d := 104) (v := arg s 2) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  obtain E₁ := E₀.of_mem R₁ (by decide) M₁
  obtain hz : 4960 ≤ (arg s 4).toNat * 8 := by omega_arith
  obtain ⟨Ip₁, Iq₁, -, -⟩ := deriveIn h rfl rfl E₁
  -- The specification's components.
  obtain hpl : (deriveParams s).length = 2 * (arg s 0).toNat + (arg s 2).toNat := by
    simp only [deriveParams, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3
  obtain hxl : (deriveX s).length = (arg s 2).toNat := by
    simp only [deriveX, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  obtain PB := paramsBytes_at s.mem (State.addr (s.gpr .r2)) (pLen := (arg s 0).toNat) (qLen := (arg s 2).toNat)
    (total := (s.gpr .r3).toNat) (by omega_arith)
  obtain spec := deriveKeyBytes_iff hv hpl hxl
  simp only [deriveParams, deriveX] at spec
  rw [PB] at spec
  dsimp only at spec
  have SR : deriveRes s = _ := spec
  unfold Generate.deriveSized
  refine WP.seq (WP.mono (check_ok E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value)
    fun t₂ ⟨Z, M, _, R₂, O₂⟩ => ?_)
  obtain E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
  obtain po : pointerValue (State.addr (arg s 3)) t₂ (.input .out) = s.gpr .r0 :=
    E₂.field (d := 96) (v := s.gpr .r0) (by simp)
  obtain ofit : (pointerValue (State.addr (arg s 3)) t₂ (.input .out)).toNat +
      (3 * (arg s 0).toNat + 2 * (arg s 2).toNat) ≤ 2 ^ 32 := by rw [po]; omega_arith
  obtain owr : ∀ i < 3 * (arg s 0).toNat + 2 * (arg s 2).toNat,
      InRegions t₂.wr (State.addr (pointerValue (State.addr (arg s 3)) t₂ (.input .out)) + BitVec.ofNat 64 i) 1 :=
    fun i hi => by
      rw [po, E₂.wr, hwr]
      exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain dOS' : Region.Disjoint ⟨State.addr (s.gpr .r0), 3 * (arg s 0).toNat + 2 * (arg s 2).toNat⟩
      ⟨State.addr (arg s 3), (arg s 4).toNat * 8⟩ := hr1 ▸ dOS
  refine WP.ite t₂.z (eval_eq _) (fun ht => ?_) (fun hf => ?_)
  · -- A rejected shape.
    obtain nv := of_decide_eq_true (Z ▸ ht)
    refine WP.mono (deriveFailure_ok E₂.ws (by omega_arith) (by omega_arith) (by omega_arith) ofit owr)
      fun t₃ ⟨Z₃, B₃, R₃, O₃⟩ => ?_
    rw [po] at B₃ O₃
    obtain none : deriveRes s = none := by rw [SR]; exact ite_eq_right fun h => nv h.1
    refine finish_ok (E₂.ws.of_rest R₃ (by decide)) (by omega_arith) (E₂.saved_outside O₃ dOS' (by omega_arith))
      (R₃.sp.trans E₂.sp) fun u A r0 Mu => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, none]; rfl
    · rw [Mu, hr1, B₃, none]; rfl
  · have valid : shapeValid _ _ := Classical.not_not.mp (of_decide_eq_false (Z ▸ hf))
    obtain ⟨Ip, Iq, Ig, Ix⟩ := deriveIn h rfl rfl E₂
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    obtain hm : maskW (State.addr (arg s 3)) t₂ = BitVec.allOnes 32 := by
      rw [M]; unfold mask32; split
      · rfl
      · next hn => exact absurd valid hn
    refine WP.seq (WP.mono (hc ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig Ix hP hPo hQ hQo)
      fun t₃ ⟨F₃, Y₃, Rn₃⟩ => ?_)
    obtain E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith)
    rw [hm, BitVec.allOnes_and, mask32_iff (hC valid)] at F₃
    obtain po₃ : pointerValue (State.addr (arg s 3)) t₃ (.input .out) = s.gpr .r0 :=
      E₃.field (d := 96) (v := s.gpr .r0) (by simp)
    obtain pp₃ : pointerValue (State.addr (arg s 3)) t₃ (.input .p) = s.gpr .r2 :=
      E₃.field (d := 64) (v := s.gpr .r2) (by simp)
    obtain px₃ : pointerValue (State.addr (arg s 3)) t₃ (.input .nonce) = arg s 1 :=
      E₃.field (d := 88) (v := arg s 1) (by simp)
    obtain K : KeySources t₃ (State.addr (arg s 3)) ((arg s 4).toNat * 8) (arg s 0).toNat (arg s 2).toNat
        (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (2 * (arg s 0).toNat + (arg s 2).toNat))
        (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat) := by
      refine ⟨E₃.ws, by omega_arith, by omega_arith, q0, by omega_arith, by simp [Spec.Rsa.bytesAt], by simp [Spec.Rsa.bytesAt], ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [pp₃]
        exact bytesIn_env E₃ (by rw [hrd, ← hr3]; simp) (by omega_arith) (dPS.sub_left (Region.sub_prefix (by omega_arith)))
      · rw [px₃]
        exact bytesIn_env E₃ (by rw [hrd]; simp) fX dXS
      · rw [po₃]; omega_arith
      · intro i hi
        rw [po₃, E₃.wr, hwr]
        exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      · rw [pp₃, po₃]; exact (hr1 ▸ dOP.symm).sub_left (Region.sub_prefix (by omega_arith))
      · rw [px₃, po₃]; exact hr1 ▸ dOX.symm
      · rw [po₃]; exact dOS'.symm
    refine WP.mono (writeKey_ok K _ F₃ (by simp only [Impl.Dsa.Layout.t2]; omega_arith))
      fun t₄ ⟨r0₄, B₄, O₄, R₄⟩ => ?_
    rw [po₃] at B₄ O₄
    rw [Y₃] at B₄
    refine finish_ok (E₃.ws.of_rest R₄ (by decide)) (by omega_arith) (E₃.saved_outside O₄ dOS' (by omega_arith))
      (R₄.sp.trans E₃.sp) fun u A r0 Mu => ⟨A, ?_, ?_⟩
    · rw [status_toNat (r0.trans r0₄), SR]
      split_ifs with hc₁ hc₂ hc₂
      · rfl
      · exact absurd ⟨valid, hc₁⟩ hc₂
      · exact absurd hc₂.2 hc₁
      · rfl
    · rw [Mu, hr1, B₄, SR]
      split_ifs with hc₁ hc₂ hc₂
      · rw [Option.getD_some, hr3]
      · exact absurd ⟨valid, hc₁⟩ hc₂
      · exact absurd hc₂.2 hc₁
      · rfl

theorem derive_correct {s : State} (h : derivePre s) :
    WP isa Generate.deriveKey s fun t => abiPreserved s t ∧ deriveArm.post s t :=
  deriveWith_correct deriveCompute_computeOk h fun _ => Iff.rfl

/-- A checked domain passes the domain's checks. -/
theorem deriveDomain_checked {s : State} (h : deriveCheckedArm.pre s) :
    domainChecks (deriveP s) (deriveQ s) (deriveG s) := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, hr3, -⟩, hc⟩ := h
  obtain hpl : (deriveParams s).length = 2 * (arg s 0).toNat + (arg s 2).toNat := by
    simp only [deriveParams, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3
  obtain e := (checkParametersBytes_iff hv hpl).mp hc
  simp only [deriveParams] at e
  rw [paramsBytes_at s.mem (State.addr (s.gpr .r2)) (pLen := (arg s 0).toNat) (qLen := (arg s 2).toNat)
    (total := (s.gpr .r3).toNat) (by omega_arith)] at e
  exact e.2

/-- `vg_dsa_derive_key_checked`: the derivation without the domain's checks,
which its precondition makes. -/
theorem deriveChecked_correct {s : State} (h : deriveCheckedArm.pre s) :
    WP isa Generate.deriveChecked s fun t => abiPreserved s t ∧ deriveCheckedArm.post s t :=
  deriveWith_correct keyCompute_computeOk h.1 fun _ =>
    ⟨fun k => ⟨deriveDomain_checked h, k⟩, fun k => k.2⟩

end VG.Proof.Dsa.Arm
