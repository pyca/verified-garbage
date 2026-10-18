module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncFrame
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP encryption on x86-64: the public operation's arguments

Its arguments (`pubArgs_ok`) and what the call reads and writes
(`pub_covers`); the call is `PcCall`'s. Memory outside the stack the
function uses, `out` and the working space reads as on entry (`FrE`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.RsaPkcs1Sig.X86_64 (PubImpl pubChk pubChkPost pubChecked)

variable {H : Spec.Mgf1.Hash}

/-- `out`. -/
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩

/-- The working space. -/
def scrR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩

/-- Memory changed only in the stack the function uses, `out` and the
working space. -/
def FrE (s : State) (m : Mem) : Prop := Frame [stkR s, outR s, scrR s] s.mem m

/-- The bytes of a region apart from those, as on entry. -/
theorem FrE.bytes {s : State} {m : Mem} (h : FrE s m) {p : Addr} {len : Nat} (hk : (stkR s).Disjoint ⟨p, len⟩)
    (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => Frame.bytes h (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- A step that changed memory only within the writable regions of a state
in the frame and the 16 bytes below it. -/
theorem FrE.step {s : State} {m m' : Mem} (h : FrE s m) {ws : List Region}
    (hws : ws = [frR s, outR s, scrR s]) (h' : Frame (ws ++ [below (fb s) 16]) m m') : FrE s m' :=
  h.trans (h'.sub fun r hr => by
    rw [hws] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., frame_sub s⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., ret_sub s⟩)

theorem EPre.wr {s : State} (hp : EPre H s) : (allocState frameBytes s).wr = [frR s, outR s, scrR s] := by
  simp [allocState, hp.hwr, outR, scrR]

theorem owned_one {stack : Nat} {e : State} {ws : List Region} (h : Owned stack e ws) {r : Region} (hr : r ∈ ws) :
    Owned stack e [r] := fun q hq => by rw [List.mem_singleton.mp hq]; exact h r hr

/-- What the function writes is the entry's own: the frame and the 16 bytes
below it are in the stack it uses, `out` and the working space writable. -/
theorem EPre.owned {s : State} (hp : EPre H s) :
    Owned encStack s [frR s, outR s, scrR s, below (fb s) 16] := by
  have hstk : Owned encStack s [stkR s] := fun r hr x hx => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s, List.mem_append_right _ (by simp [abi, encStack, stackBelow, stkR]), hx⟩
  have hw : ∀ r ∈ s.wr, Owned encStack s [r] := fun r hr q hq x hx => by
    rw [List.mem_singleton] at hq; subst hq
    exact ⟨q, List.mem_append_left _ hr, hx⟩
  exact (hstk.sub (frame_sub s)).cons ((hw _ (by simp [hp.hwr, outR])).cons
    ((hw _ (by simp [hp.hwr, scrR])).cons (hstk.sub (ret_sub s))))

theorem EPre.scrO {s : State} (hp : EPre H s) : Owned encStack s [⟨stackArg s 6, oRsa⟩] := by
  have := hp.hsl; have := hp.k1
  exact (owned_one hp.owned (r := scrR s) (by simp)).sub (Region.sub_prefix (by unfold oRsa; omega))

theorem EPre.sp16 {s : State} (hp : EPre H s) : 16 ≤ (fb s).toNat := by
  have := fb_toNat hp; have := hp.sp1; unfold encStack frameBytes at *; omega

/-! ## The arguments -/

theorem pubArgs_ok {s u : State} (L : Lay u (fb s) (stackArg s 6)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 6) V W) (hW : ∀ k, 21 ≤ k → k ≤ 26 → W k = encW s k) :
    WP isa (.block pubArgs) u fun u' => Lay u' (fb s) (stackArg s 6) ∧
      Keep [.rax, .rdx, .rcx, .r9, .rdi, .rsi, .r8] u u' ∧
      Rep u'.mem (fb s) (stackArg s 6) V (upd (upd (upd (upd W 0 (off (stackArg s 6) oEm)) 1 (s.gpr .rcx)) 2
        (off (stackArg s 6) oRsa)) 3 (stackArg s 7 - 1024)) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9 := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have G' := L.geo
  have e : ∀ k, 21 ≤ k → k ≤ 26 → W k = encW s k := hW
  have w21 : W 21 = s.gpr .rdi := (e 21 (by omega) (by omega)).trans (by simp [encW, fnW, selW, encPW, upd])
  have w22 : W 22 = s.gpr .rdx := (e 22 (by omega) (by omega)).trans (by simp [encW, fnW, selW, encPW, upd])
  have w23 : W 23 = s.gpr .rcx := (e 23 (by omega) (by omega)).trans (by simp [encW, fnW, selW, encPW, upd])
  have w24 : W 24 = s.gpr .r8 := (e 24 (by omega) (by omega)).trans (by simp [encW, fnW, selW, encPW, upd])
  have w25 : W 25 = s.gpr .r9 := (e 25 (by omega) (by omega)).trans (by simp [encW, fnW, selW, encPW, upd])
  have w26 : W 26 = stackArg s 7 := (e 26 (by omega) (by omega)).trans (by simp [encW, fnW, selW, encPW, upd])
  have R1 := (((R.wf G' (k := 0) (by decide) (off (stackArg s 6) oEm)).wf G' (k := 1) (by decide) (s.gpr .rcx)).wf G'
    (k := 2) (by decide) (off (stackArg s 6) oRsa)).wf G' (k := 3) (by decide) (stackArg s 7 - 1024)
  have z : off (fb s) (8 * 0) = fb s := BitVec.add_zero _
  rw [z, show 8 * 1 = 8 from rfl, show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl] at R1
  have h0 : InRegions u.wr (fb s) 8 := by rw [← z]; exact L.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r9, .rdi, .rsi, .r8] (Q := fun u' => u'.mem =
      (((u.mem.writeW (fb s) (off (stackArg s 6) oEm)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
        (off (fb s) 16) (off (stackArg s 6) oRsa)).writeW (off (fb s) 24) (stackArg s 7 - 1024) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9) ?_ rfl) fun u' ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, kk⟩ =>
    ⟨L.of_rep' R (by rw [hm]; exact R1) (by simp [upd]) (kk.gpr (by decide)) kk.2.2, kk, by rw [hm]; exact R1,
      h1, h2, h3, h4, h5, h6⟩
  xrun [pubArgs, scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), L.ld (d := sScrLen) (by decide),
    L.ld (d := sOut) (by decide), L.ld (d := sN) (by decide), L.ld (d := sE) (by decide),
    L.ld (d := sEl) (by decide), hs, R.slot (d := sK) (k := 23) rfl (by decide) w23,
    R.slot (d := sScrLen) (k := 26) rfl (by decide) w26,
    h0, L.st (d := 8) (by decide), L.st (d := 16) (by decide), L.st (d := 24) (by decide),
    R1.slot (d := sOut) (k := 21) rfl (by decide) (v := s.gpr .rdi) (by simp [upd, w21]),
    R1.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .rcx) (by simp [upd, w23]),
    R1.slot (d := sN) (k := 22) rfl (by decide) (v := s.gpr .rdx) (by simp [upd, w22]),
    R1.slot (d := sE) (k := 24) rfl (by decide) (v := s.gpr .r8) (by simp [upd, w24]),
    R1.slot (d := sEl) (k := 25) rfl (by decide) (v := s.gpr .r9) (by simp [upd, w25]),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
    show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 from by decide]

/-! ## The call -/

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {t : State} {F : Addr} (hsp : t.gpr .rsp = F) (hF : 8 ≤ F.toNat) (rd wr : List Region)
    {i : Nat} (hi : F.toNat + 8 * i + 8 ≤ 2 ^ 64) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (off F (8 * i)) 64 := by
  have hb : F - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off F (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  have hsep := Offset.sep (F - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show F - 8 + BitVec.ofNat 64 0 = F - 8 from BitVec.add_zero _, hb] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, hb]
  exact Mem.readW_writeW_sep hsep (by decide)

/-- The working space the call gets: ours ends at `oRsa`. -/
def rsaR (s : State) : Region := ⟨off (stackArg s 6) oRsa, (stackArg s 7 - 1024).toNat * 8⟩

/-- What the call reads: `n`, `e`, `EM` and its stack arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (stackArg s 6) oEm, (s.gpr .rcx).toNat⟩,
    ⟨fb s, 32⟩]

/-- What it writes: `out` and the rest of the working space. -/
def pubWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, rsaR s]

theorem rsa_toNat {s : State} (hp : EPre H s) :
    (stackArg s 7 - 1024).toNat = (stackArg s 7).toNat - 1024 ∧
      (off (stackArg s 6) oRsa).toNat = (stackArg s 6).toNat + oRsa := by
  have := hp.hsl; have := hp.wS; have := hp.k1
  constructor
  · rw [BitVec.toNat_sub, show (1024 : BitVec 64).toNat = 1024 from rfl]; omega
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa; omega

theorem rsa_sub {s : State} (hp : EPre H s) : Region.Sub (rsaR s) (scrR s) := by
  have ⟨h1, h2⟩ := rsa_toNat hp
  have := hp.hsl
  simp only [rsaR, scrR]
  rw [h1]
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem em_sub {s : State} (hp : EPre H s) : Region.Sub ⟨off (stackArg s 6) oEm, (s.gpr .rcx).toNat⟩ (scrR s) := by
  have := hp.hsl; have := hp.k2
  exact Offset.sub_base _ (by unfold oEm; omega)

theorem pub_covers {s t : State} (hp : EPre H s) (hrd : t.rd = s.rd) (hwr : t.wr = [frR s, outR s, scrR s]) :
    Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hsi := hp.hsi
  have ⟨r1, r2⟩ := rsa_toNat hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, rsaR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hwr]
    rcases hr with rfl | rfl
    · exact ⟨outR s, by simp, 0, z _, by simp only [outR]; omega⟩
    · exact ⟨scrR s, by simp, oRsa, rfl, by simp only [scrR]; rw [r1]; unfold oRsa; omega⟩
  have cr : Covers (rdL H s) (t.rd ++ t.wr) := by rw [hrd]; exact hp.hrd.left
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) cw.right, cw⟩
  simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [rdL])).trans cr
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp [rdL])).trans cr
  · refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨scrR s, List.mem_append_right _ (by rw [hwr]; simp), oEm, rfl, by simp only [scrR]; unfold oEm; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨frR s, List.mem_append_right _ (by rw [hwr]; simp), 0, z _, by dsimp only; unfold frameBytes; omega⟩

end VG.Proof.RsaOaep.X86_64
