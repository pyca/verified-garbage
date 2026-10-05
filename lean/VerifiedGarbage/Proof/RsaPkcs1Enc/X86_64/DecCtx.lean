import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPriv

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: after the private-key operation

From the call of the private-key operation to the output, the function
writes only the first `scrBytes` bytes of `scratch`, its slots from `oR` on
and the stack below its frame (`Safe`): through all of it, the slots, the
result `R` in its slot and `EM` in `out` stay as they are (`Ctx`,
`Ctx.step`). What it computes in `scratch` is tracked with the regions each
step writes (`bytes_keep`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- `scratch`, and an address in it. -/
abbrev sc (s : State) : Addr := stackArg s 15
abbrev scA (s : State) (d : Nat) : Addr := off (sc s) d

/-- The part of `scratch` used after the private-key operation. -/
def scrBytes : Nat := 3440

theorem scr_len {s : State} (hp : DPre s) : scrBytes ≤ (stackArg s 16).toNat * 8 ∧
    (sc s).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64 := by
  have := hp.hsl; have := hp.k1; have := hp.wS
  exact ⟨by unfold scrBytes; omega, by omega⟩

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- What a step may write. -/
def Safe (s : State) (r : Region) : Prop :=
  Region.Sub r ⟨sc s, scrBytes⟩ ∨ Region.Sub r (below (fb s) (8 + privStack)) ∨ Region.Sub r ⟨off (fb s) oI, 16⟩

/-- After the call: the slots, `R` in its slot, `EM` in `out`. -/
structure Ctx (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame (wrs s) s.mem t.mem
  slots : Slots s t.mem
  sR : word t.mem (fb s) oR = R
  out : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s) = EM

theorem Safe.sub {s : State} (hp : DPre s) {r : Region} (h : Safe s r) : ∃ R ∈ wrs s, Region.Sub r R := by
  rcases h with h | h | h
  · obtain ⟨h1, _⟩ := scr_len hp
    exact ⟨scrR s, by simp, sub_trans h (Region.sub_prefix h1)⟩
  · exact ⟨stkR s, by simp, sub_trans h (below_sub s (le_refl _))⟩
  · exact ⟨stkR s, by simp, sub_trans h (frame_sub s (by decide))⟩

/-- A region apart from the stack the function uses and from `scratch` is
apart from what a step writes. -/
theorem Safe.disj {s : State} (hp : DPre s) {r X : Region} (h : Safe s r) (hk : (stkR s).Disjoint X)
    (hs : (scrR s).Disjoint X) : X.Disjoint r := by
  rcases h with h | h | h
  · obtain ⟨h1, _⟩ := scr_len hp
    exact (hs.sub_left (sub_trans h (Region.sub_prefix h1))).symm
  · exact (hk.sub_left (sub_trans h (below_sub s (le_refl _)))).symm
  · exact (hk.sub_left (sub_trans h (frame_sub s (by decide)))).symm

/-- Words of the frame below `oI` are apart from what a step writes. -/
theorem Safe.slot {s : State} (hp : DPre s) {r : Region} (h : Safe s r) {d : Nat} (hd : d + 8 ≤ oI) :
    (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have hF := fb_toNat hp
  have e1 : oI = 200 := rfl
  rcases h with h | h | h
  · obtain ⟨h1, _⟩ := scr_len hp
    exact (hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega))).sub_right (sub_trans h (Region.sub_prefix h1))
  · refine Region.Disjoint.sub_right ?_ h
    exact Offset.disjoint_below (fb s) (by have := hF.2.2; unfold frameBytes privStack at *; omega)
  · refine Region.Disjoint.sub_right ?_ h
    exact Offset.disjoint _ (.inl hd) (by unfold frameBytes at hF; omega) (by unfold frameBytes at hF; omega)

/-- `[b + i + d]` for `b = p` and `i = j`. -/
theorem ea_bxd {t : State} {b i : Reg} {p : Addr} {j : Nat} (d : Nat) (hb : t.gpr b = p)
    (hi : t.gpr i = BitVec.ofNat 64 j) : t.ea (bx b i d) = off p (d + j) := by
  simp only [State.ea, bx, hb, hi, BitVec.mul_one, BitVec.ofInt_natCast, off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

/-- `[b + d]`. -/
theorem ea_at {t : State} {b : Reg} {p : Addr} (d : Nat) (hb : t.gpr b = p) : t.ea (at_ b d) = off p d := by
  simp only [State.ea, at_, hb, BitVec.ofInt_natCast, off]

theorem blen (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem bget (m : Mem) (p : Addr) {n i : Nat} (h : i < (Spec.Rsa.bytesAt m p n).length) :
    (Spec.Rsa.bytesAt m p n)[i] = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt]

/-- A buffer apart from what a step writes keeps its bytes. -/
theorem bytes_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

/-- A step that writes only where it may keeps `Ctx`. -/
theorem Ctx.step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.gpr .rsp = t.gpr .rsp) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe s r) : Ctx s R EM t' := by
  have w : ∀ {d : Nat}, d + 8 ≤ oI → word t'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf.readW (Region.contains_self _ _) (fun r hr => Safe.slot hp (hs r hr) hd) (by decide)
  have hk2 := hp.k2
  have hsi := hp.hsi
  refine ⟨hsp.trans hc.rsp, hrd.trans hc.rd, hwr.trans hc.wr, frame_call hc.mem hf fun r hr => (hs r hr).sub hp,
    ⟨(w (by decide)).trans hc.slots.sOut, (w (by decide)).trans hc.slots.sML, (w (by decide)).trans hc.slots.sN,
      (w (by decide)).trans hc.slots.sK, (w (by decide)).trans hc.slots.sE, (w (by decide)).trans hc.slots.sEl,
      (w (by decide)).trans hc.slots.sD, (w (by decide)).trans hc.slots.sDl, (w (by decide)).trans hc.slots.sIn,
      (w (by decide)).trans hc.slots.sScr⟩, (w (by decide)).trans hc.sR, ?_⟩
  rw [bytes_keep hf (fun r hr => Safe.disj hp (hs r hr) (by have := hp.dKo; rwa [hsi] at this)
    (by have := hp.dOs; rw [hsi] at this; exact this.symm)) (by unfold kOf; omega)]
  exact hc.out

/-- `m'` differs from `m` only at the offsets `[o, o + n)` of `base`, a
region. -/
theorem frame_of_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hn : o + n ≤ 2 ^ 64) : Frame [⟨off base o, n⟩] m m' := fun x hx => by
  refine h x ?_
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains, off] at hc
  have hc' : ¬ (x - (base + BitVec.ofNat 64 o)).toNat < n := by omega
  rw [Offset.lt_iff x base hn] at hc'
  simp only [ofs]
  omega

/-- The used part of `scratch` is working space. -/
theorem Ctx.scr {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    Scr t (sc s) scrBytes := by
  obtain ⟨h1, h2⟩ := scr_len hp
  have hs : Scr t (sc s) ((stackArg s 16).toNat * 8) :=
    Scr.of_mem (by rw [hc.wr, hp.hwr]; simp) h2
  have := hs.sub (o := 0) (n := scrBytes) (by omega) (by decide)
  rwa [off_zero] at this

/-- The frame is working space. -/
theorem Ctx.frm {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [hc.wr]; exact List.mem_cons_self ..) (by have := (fb_toNat hp).1; omega)

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
