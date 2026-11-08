module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.OpenTo
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on PPC64LE: decryption from a source to a destination

Untrusted: everything here is checked by Lean. `oneCryptTo` decrypts the
`len` bytes at the source (`r27`) to the destination (`[sp + 120]`), apart
from it (`oneCryptTo_ok`), in one pass: the whole blocks by
`vg_aes_ctr32_to` (`to_call`), and the last bytes by `open`'s own tail with
`to` (`cryptTailWith_ok`, from `whole_tail`), which XORs them from the
source into the destination.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Impl.AesGcm.PPC64LE.OpenTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 inc32 gctr)
open VG.Proof.Gcm (Ctr xorKs)

/-! ## `vg_aes_ctr32_to` -/

/-- What a call of `vg_aes_ctr32_to(schedule, rounds, counter, src, n, dst)` needs. -/
structure ToCall (s : State) (K C S D : Addr) (R n : Nat) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = C
  r6 : s.gpr .r6 = S
  r7 : s.gpr .r7 = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = D
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n_lt : n < 2 ^ 64
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  sd : (⟨S, 16 * n⟩ : Region).Disjoint ⟨D, 16 * n⟩
  sfit : S.toNat + 16 * n ≤ 2 ^ 64
  dfit : D.toNat + 16 * n ≤ 2 ^ 64
  reads : Covers ([⟨K, 240⟩, ⟨S, 16 * n⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩] s.wr

/-- What a call of `vg_aes_ctr32_to` leaves. -/
structure ToPost (s : State) (K C S D : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩] s.mem s'.mem
  out : blocksAt s'.mem D n =
    ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C) (blocksAt s.mem S n)
  ctr : blockAt s'.mem C = Nat.repeat inc32 n (blockAt s.mem C)

theorem ToCall.pre {s : State} {K C S D : Addr} {R n : Nat} (h : ToCall s K C S D R n) :
    Proof.Aes.ctr32ToPPC64LE.pre
      (s.callEntry.withRegions [⟨K, 240⟩, ⟨S, 16 * n⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩]) := by
  simp only [Proof.Aes.ctr32ToPPC64LE, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, toNat64 h.n_lt, toNat_rounds h.rounds]
  exact ⟨by trivial, by trivial, h.kd, h.cd, h.sd, h.sfit, h.dfit, h.rounds⟩

theorem to_call {name : String} {s : State} {K C S D : Addr} {R n : Nat} (h : ToCall s K C S D R n) :
    WP isa (.call name Impl.Aes.PPC64LE.ctr32To) s (ToPost s K C S D R n) := by
  refine WP.call (k := Proof.Aes.ctr32ToPPC64LE) Proof.Aes.PPC64LE.ctr32To_correct
    (rd := [⟨K, 240⟩, ⟨S, 16 * n⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_, ?_⟩ <;>
  simp only [Proof.Aes.ctr32ToPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, toNat64 h.n_lt, toNat_rounds h.rounds] at hpost
  exacts [hpost.1, hpost.2]

/-- Calls of `vg_aes_ctr32_to` with the same arguments in both runs are constant time. -/
theorem to_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C S D R n, ToCall s₁ K C S D R n ∧ ToCall s₂ K C S D R n ∧
      s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Aes.PPC64LE.ctr32To) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Addr × Nat × Nat) (s₁ s₂ : State) =>
      ToCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧
        ToCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, S, D, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, C, S, D, R, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C, S, D, R, n⟩ := x
  refine RelCT.call Proof.Aes.PPC64LE.ctr32To_correct Proof.Aes.PPC64LE.ctr32To_ct [⟨K, 240⟩, ⟨S, 16 * n⟩]
    [⟨C, 16⟩, ⟨D, 16 * n⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32ToPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₁.r8, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The whole blocks -/

/-- The split of the source into whole blocks and the last bytes, and the
destination advanced past the whole blocks. -/
theorem splitTo_ok {s : State} {S D : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h24 : s.gpr .r24 = S) (h25 : s.gpr .r25 = BitVec.ofNat 64 n) (h26 : s.gpr .r26 = D) :
    WP isa (.block splitTo) s fun s' =>
      s'.gpr .r6 = S ∧ s'.gpr .r7 = BitVec.ofNat 64 (n / 16) ∧ s'.gpr .r10 = D ∧
      s'.gpr .r24 = S + BitVec.ofNat 64 (16 * (n / 16)) ∧
      s'.gpr .r25 = BitVec.ofNat 64 (n - 16 * (n / 16)) ∧
      s'.gpr .r26 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r24 → r ≠ .r25 →
        r ≠ .r26 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h24' : s.gpr .r24 = S + BitVec.ofNat 64 0 := by rw [h24]; exact (BitVec.add_zero S).symm
  have h25' : s.gpr .r25 = BitVec.ofNat 64 (n - 0) := by rw [h25, Nat.sub_zero]
  rw [splitTo, WP.block_append_iff]
  refine WP.mono (splitCtr_ok (Nat.zero_le n) hn h24' h25') fun s₁ ⟨h6, h7, h24₁, h25₁, h9, hg₁, hk₁⟩ => ?_
  have h26₁ : s₁.gpr .r26 = D := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h26]
  simp only [Nat.sub_zero, Nat.zero_add, BitVec.add_zero] at h6 h7 h24₁ h25₁ h9
  crun [h26₁, h9, h6, h7, h24₁, h25₁, mov, BitVec.or_self]
  exact ⟨fun r a b c d e f g i j => by simp [f, j, hg₁ r a b c d e g i],
    ⟨hk₁.mem, hk₁.rd, hk₁.wr, hk₁.sp, hk₁.lr⟩⟩

/-- Before `cryptTo`: the `n` bytes at `S` (`r24`) to decrypt to `D` (`r26`),
apart from it, `R` rounds in `r28`. -/
structure ToIn (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (S D : Addr) (n : Nat) (s : State) : Prop where
  env : Env V sp s
  r24 : s.gpr .r24 = S
  r25 : s.gpr .r25 = BitVec.ofNat 64 n
  r26 : s.gpr .r26 = D
  r28 : V .r28 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  src : DataOk (V .r30) (V .r31) s S n
  dst : DataW (V .r29) (V .r30) (V .r31) s D n
  sd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- After the whole blocks, from `s₀`. -/
structure WholeOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (S D : Addr) (n : Nat) (s₀ s : State) : Prop where
  env : Env V sp s
  r24 : s.gpr .r24 = S + BitVec.ofNat 64 (16 * (n / 16))
  r25 : s.gpr .r25 = BitVec.ofNat 64 (n - 16 * (n / 16))
  r26 : s.gpr .r26 = D + BitVec.ofNat 64 (16 * (n / 16))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  out : blocksAt s.mem D (n / 16) = ctr32 (ciphOf s₀.mem (V .r29) R)
    (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48)) (blocksAt s₀.mem S (n / 16))
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) =
    Nat.repeat inc32 (n / 16) (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  frame : Frame [⟨V .r30 + BitVec.ofNat 64 48, 16⟩, ⟨D, 16 * (n / 16)⟩] s₀.mem s.mem

/-- The arguments of `vg_aes_ctr32_to` but the source and the number of blocks. -/
theorem toArgs_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) {R : Nat}
    (hR : V .r28 = BitVec.ofNat 64 R) :
    WP isa (.block toArgs) s fun s' =>
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = BitVec.ofNat 64 R ∧ s'.gpr .r5 = V .r30 + BitVec.ofNat 64 48 ∧
      s'.gpr .r8 = s.gpr .r10 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h28 := he.r28; have h29 := he.r29; have h30 := he.r30
  simp only [toArgs]
  crun [h28, h29, h30, hR, mov, BitVec.or_self]
  exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32_to` on the whole blocks of the `n` bytes
at `S`, to `D`. -/
theorem toCall_mk {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {S D : Addr} {n : Nat} {s : State}
    (he : Env V sp s) (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = BitVec.ofNat 64 R)
    (h5 : s.gpr .r5 = V .r30 + BitVec.ofNat 64 48) (h6 : s.gpr .r6 = S) (h7 : s.gpr .r7 = BitVec.ofNat 64 (n / 16))
    (h8 : s.gpr .r8 = D) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hsrc : DataOk (V .r30) (V .r31) s S n)
    (hdst : DataW (V .r29) (V .r30) (V .r31) s D n) (hsd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) :
    ToCall s (V .r29) (V .r30 + BitVec.ofNat 64 48) S D R (n / 16) := by
  have h16 : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hn := hdst.ok.lt
  refine ⟨h3, h4, h5, h6, h7, h8, hR, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hdst.ctx.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix h16)
  · exact ((hdst.ok.st.sub_left (Region.sub_prefix h16)).sub_right (Lay.stSub (by decide))).symm
  · exact (hsd.sub_left (Region.sub_prefix h16)).sub_right (Region.sub_prefix h16)
  · have := hsrc.fit; omega
  · have := hdst.ok.fit; omega
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_prefix hsrc.rd h16) (Covers.cons (covers_left (he.perm.stC (by decide)))
        (Covers.cons (covers_left (covers_prefix hdst.wr h16)) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons (covers_prefix hdst.wr h16) Covers.nil)

/-- The whole blocks at the source, decrypted to the destination. -/
theorem wholeTo_ok {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {S D : Addr} {n : Nat} {s : State}
    (h : ToIn V sp R S D n s) : WP isa wholeTo s (WholeOut V sp R S D n s) := by
  have hn := h.dst.ok.lt
  have h16 : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine wholeWith_ok (nb := n / 16) (by omega) (splitTo_ok hn h.r24 h.r25 h.r26) (fun _ h => h.2.1)
    (fun s₁ ⟨_, _, _, h24, h25, h26, hg₁, hk₁⟩ h0 => ?_) (fun s₁ ⟨h6, h7, h10, h24, h25, h26, hg₁, hk₁⟩ _ => ?_)
  all_goals have he₁ : Env V sp s₁ := h.env.keep (fun r hr => hg₁ r (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
  · refine ⟨he₁, h24, h25, h26, hk₁.rd, hk₁.wr, ?_, ?_, ?_⟩
    · simp only [h0, Spec.Gcm.blocksAt, List.range_zero, List.map_nil, Spec.Gcm.ctr32, Spec.Gcm.keystream,
        List.length_nil, List.zipWith_nil_left]
    · rw [h0, hk₁.mem]; rfl
    · rw [hk₁.mem]; exact Frame.refl _ _
  · refine WP.seq (WP.mono (toArgs_ok he₁ h.r28) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_)
    have he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    have hdst := h.dst.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr)
    have hsrc := h.src.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr)
    have hcall := toCall_mk he₂ a3 a4 a5 (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7]) (by rw [a8, h10]) h.rounds hsrc hdst h.sd
    refine WP.mono (to_call hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem] at gout gctr gframe
    refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, by rw [g.rd, hk₂.rd, hk₁.rd],
      by rw [g.wr, hk₂.wr, hk₁.wr], gout, gctr, gframe⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h25]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h26]

/-! ## `cryptTo` -/

/-- After `cryptTo`, from `m₀`: the destination holds the source decrypted
from the counter block `icb`. -/
structure ToOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (S D : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : blockAt m₀ (V .r30 + BitVec.ofNat 64 48) = icb →
    bytesAt s.mem D n = gctr (ciphOf m₀ (V .r29) R) icb (bytesAt m₀ S n)
  frame : Frame (crFrame (V .r30) (V .r31) D n) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {S D : Addr} {n : Nat} {s₀ : State}

variable (L : Lay (V .r29) (V .r30) (V .r31))
include L

/-- After the whole blocks, the last bytes to go from the source to the
destination, `open`'s tail with `to`. -/
theorem whole_tail {icb : Block} {s₁ : State} (hs : ToIn V sp R S D n s₀) (h : WholeOut V sp R S D n s₀ s₁) :
    TailIn true V sp R icb (16 * (n / 16)) (S + BitVec.ofNat 64 (16 * (n / 16)))
      (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (ciphOf s₀.mem (V .r29) R)
      (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48) = icb) s₁ := by
  have hn := hs.dst.ok.lt
  have h16 : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have dC : ∀ r ∈ [(⟨V .r30 + BitVec.ofNat 64 48, 16⟩ : Region), ⟨D, 16 * (n / 16)⟩],
      (⟨V .r29, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact hs.dst.ctx.sub_right (Region.sub_prefix h16)
  refine ⟨h.env, h.r24, h.r25, fun _ => h.r26, hs.r28, hs.rounds, .inr (by omega),
    (hs.src.of_eq h.rd h.wr).drop h16, (hs.dst.of_eq h.rd h.wr).drop h16, (fun h => nomatch h),
    .inr ((hs.sd.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))),
    ciph_frame h.frame dC hs.rounds, fun hcb => ?_⟩
  have := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s₀.mem (V .r30 + BitVec.ofNat 64 48)
    (V .r30 + BitVec.ofNat 64 64) (ciphOf s₀.mem (V .r29) R) hcb) (by decide) h.out h.cb).2
  rwa [Nat.zero_add] at this

/-- `cryptTo`: the source decrypted to the destination, in one pass. -/
theorem cryptTo_ok {icb : Block} (h : ToIn V sp R S D n s₀) :
    WP isa cryptTo s₀ (ToOut V sp R icb S D n s₀.mem) := by
  have hn := h.dst.ok.lt
  have h16 : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  refine WP.ite (decide (n = 0)) (eval_zero h.r25 hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨h.env, fun _ => ?_, Frame.refl _ _⟩
    rw [Proof.Gcm.gctr_eq]; simp [bytesAt]; rfl
  · refine WP.seq (WP.mono (wholeTo_ok h) fun s₁ hw => ?_)
    refine WP.mono (cryptTailWith_ok L (whole_tail L (icb := icb) h hw) (by omega)) fun s₂ o =>
      ⟨o.env, fun hcb => ?_, ?_⟩
    · have hcw := (Proof.Gcm.ctr_wholeTo (Proof.Gcm.ctr_zero s₀.mem (V .r30 + BitVec.ofNat 64 48)
        (V .r30 + BitVec.ofNat 64 64) (ciphOf s₀.mem (V .r29) R) hcb) (by decide) hw.out hw.cb).1
      have hdone : bytesAt s₂.mem D (16 * (n / 16)) = bytesAt s₁.mem D (16 * (n / 16)) := by
        refine bytesAt_frame o.frame (fun r hr => ?_) (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact split_disj h16 hn
        · exact (h.dst.ok.st.sub_left (Region.sub_prefix h16)).sub_right (Lay.stSub (by decide))
        · exact (h.dst.ok.w.sub_left (Region.sub_prefix h16)).sub_right (Lay.wSub (by decide))
      have hsrc : bytesAt s₁.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s₀.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        refine bytesAt_frame hw.frame (fun r hr => ?_) (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (h.src.st.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.stSub (by decide))
        · exact (h.sd.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix h16)
      have key := done_appendTo (P := 0) (hdone.trans hcw) (by rw [Nat.zero_add, o.out hcb, hsrc])
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at key
      rw [Proof.Gcm.gctr_eq]; exact key
    · refine (hw.frame.sub fun r hr => ?_).trans (o.frame.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix h16⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

end

/-! ## `oneCryptTo` -/

/-- The data, its length and the destination, loaded from `sp + 120`. -/
theorem dataTo_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} {D : Addr} (he : Env V sp s)
    (hi : InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 120) 8)
    (hv : s.mem.readW (sp + BitVec.ofNat 64 120) 64 = D) :
    WP isa (.block dataTo) s fun s' =>
      s'.gpr .r24 = V .r27 ∧ s'.gpr .r25 = BitVec.ofNat 64 (V .r23).toNat ∧ s'.gpr .r26 = D ∧
        (∀ r, r ≠ .r12 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h27 := he.fr .r27 (by decide)
  have h23 := he.ofNat (r := .r23) (by decide)
  have hsp := he.sp
  have h₁ : WP isa (.block [mov .r24 .r27, mov .r25 .r23, .addSp .r12 0]) s fun s₁ =>
      s₁.gpr .r24 = V .r27 ∧ s₁.gpr .r25 = BitVec.ofNat 64 (V .r23).toNat ∧ s₁.gpr .r12 = s.sp ∧
        (∀ r, r ≠ .r12 → r ≠ .r24 → r ≠ .r25 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    crun [mov, BitVec.or_self, h27, h23]
    exact ⟨fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  rw [show dataTo = [mov .r24 .r27, mov .r25 .r23, .addSp .r12 0] ++ [.load .d .r26 .r12 120] from rfl]
  refine WP.block_append (WP.mono h₁ fun s₁ ⟨a24, a25, a12, g₁, k₁⟩ => ?_)
  refine WP.mono (ld_ok (t := .r26) (v := D) (by decide) (by decide) (by decide) (by rw [a12, k₁.rd, k₁.wr, hsp]; exact hi)
    (by rw [a12, k₁.mem, hsp]; exact hv)) fun s₂ ⟨h26, g₂, k₂⟩ => ?_
  refine ⟨by rw [g₂ _ (by decide), a24], by rw [g₂ _ (by decide), a25], h26, fun r a b c d => ?_, k₁.trans k₂⟩
  rw [g₂ r d, g₁ r a b c]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

/-- `oneCryptTo`: the data (`len`, `r23`, bytes at `r27`) decrypted to the
destination at `[sp + 120]`, apart from it, from the counter block `icb`. -/
theorem oneCryptTo_ok {R : Nat} {s : State} {D : Addr} (he : Env V sp s) (h28 : V .r28 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs : DataOk (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hd : DataW (V .r29) (V .r30) (V .r31) s D (V .r23).toNat)
    (hsd : (⟨V .r27, (V .r23).toNat⟩ : Region).Disjoint ⟨D, (V .r23).toNat⟩)
    (hi : InRegions (s.rd ++ s.wr) (sp + BitVec.ofNat 64 120) 8)
    (hv : s.mem.readW (sp + BitVec.ofNat 64 120) 64 = D) {icb : Block} :
    WP isa oneCryptTo s (ToOut V sp R icb (V .r27) D (V .r23).toNat s.mem) := by
  refine WP.seq (WP.mono (dataTo_ok he hi hv) fun s₁ ⟨a24, a25, a26, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) k₁.sp k₁.rd k₁.wr
  have ti : ToIn V sp R (V .r27) D (V .r23).toNat s₁ :=
    ⟨he₁, a24, a25, a26, h28, hR, hs.of_eq k₁.rd k₁.wr, hd.of_eq k₁.rd k₁.wr, hsd⟩
  have := cryptTo_ok L (icb := icb) ti
  rwa [k₁.mem] at this

end

end VG.Proof.AesGcm.PPC64LE
