module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecBase
public import VerifiedGarbage.Proof.Hmac.Generic.Common
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `scratch`

The parts of `scratch` the function uses (`sc P o n`, its `n` bytes from
offset `o`, all within its first 8448 bytes, which every `scratch` has), and
where they are: apart from each other as their offsets say (`sc_sep`), from
the frames and the stack below (`In.fr_sc`, `In.low_sc`), and from the other
buffers (`In.sc_ro`, `In.sc_out`, `In.sc_ml`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm

variable {P : EP} {σ : State}

/-- The `n` bytes of `scratch` from offset `o`. -/
abbrev sc (P : EP) (o n : Nat) : Region := ⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩

namespace In

variable (h : In P σ)
include h

theorem sl8 : 8448 ≤ P.sl * 8 := by
  have := h.slK; have := h.k64; simp only [Spec.Rsa.scratchWords] at *; omega

theorem scr_fit : P.scr.toNat + P.sl * 8 ≤ 2 ^ 32 := by
  have := h.ok.fits P.SCR (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this

theorem scrA {o : Nat} (ho : o < 8448) : State.addr (P.scr + BitVec.ofNat 32 o) = State.addr P.scr + BitVec.ofNat 64 o :=
  addr_add (by have := h.scr_fit; have := h.sl8; omega)

theorem scr_toNat {o : Nat} (ho : o < 8448) : (P.scr + BitVec.ofNat 32 o).toNat = P.scr.toNat + o := by
  have := h.scr_fit; have := h.sl8
  rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sc_sub {o n : Nat} (hn : o + n ≤ 8448) : Region.Sub (sc P o n) P.SCR :=
  Offset.sub_base _ (by have := h.sl8; omega)

theorem sc_ro {o n : Nat} (hn : o + n ≤ 8448) {R : Region} (hR : R ∈ P.lay.ro) : (sc P o n).Disjoint R :=
  (h.ok.rw_ro (w := P.SCR) (by simp) hR).sub_left (h.sc_sub hn)

theorem sc_out {o n : Nat} (hn : o + n ≤ 8448) : (sc P o n).Disjoint P.OUT := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact (this.1.2.symm).sub_left (h.sc_sub hn)

theorem sc_ml {o n : Nat} (hn : o + n ≤ 8448) : (sc P o n).Disjoint P.ML := by
  have := h.ok.wrw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at this
  exact (this.2.1.symm).sub_left (h.sc_sub hn)

theorem fr_sc {d k o n : Nat} (hd : d + k ≤ frameBytes + 56) (hn : o + n ≤ 8448) :
    Region.Disjoint ⟨P.lay.fr d, k⟩ (sc P o n) :=
  (h.ok.stk_fr (R := P.SCR) (.inr (by simp)) hd).sub_right (h.sc_sub hn)

theorem low_sc {o n : Nat} (hn : o + n ≤ 8448) : P.lay.LOW.Disjoint (sc P o n) :=
  (h.ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right (h.sc_sub hn)

theorem fit_sc {o n : Nat} (hn : o + n ≤ 8448) (ho : o < 8448) : (P.scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
  rw [h.scr_toNat (by omega)]; have := h.scr_fit; have := h.sl8; omega

end In

theorem sc_sep {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o) (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) :
    (sc P o n).Disjoint (sc P o' n') :=
  Offset.disjoint _ hs (by omega) (by omega)

theorem St.sc_w {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) :
    InRegions s.wr (State.addr P.scr + BitVec.ofNat 64 o) n :=
  ⟨P.SCR, by rw [hs.2.wr, hs.1.ok.wr]; simp, Offset.contains_base _ (by have := hs.1.sl8; omega) (by omega)⟩

theorem St.sc_r {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) :
    InRegions (s.rd ++ s.wr) (State.addr P.scr + BitVec.ofNat 64 o) n :=
  let ⟨r, hr, hc⟩ := St.sc_w hs hn
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A streaming state keeps what it represents while memory changes elsewhere. -/
theorem repr_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) {msg : List Byte} (h : Spec.Sha256.Repr m p msg) :
    Spec.Sha256.Repr m' p msg :=
  Proof.Hmac.Generic.Common.sha256_repr m m' p p msg (fun i hi => hf.bytes (R := ⟨p, 96⟩) hd (by show 96 ≤ 2 ^ 64; decide) hi) h

/-- A byte string keeps its bytes while memory changes elsewhere. -/
theorem bytes_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' R.base R.len = Spec.Rsa.bytesAt m R.base R.len :=
  bytesAt_frame hf hd hl

end VG.Proof.RsaPkcs1Enc.Arm.Dec
