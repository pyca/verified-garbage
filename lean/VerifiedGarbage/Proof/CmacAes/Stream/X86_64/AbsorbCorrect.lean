import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbBlocks

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = D
  r8 : (s₀.gpr .r8).toNat = L
  r9 : s₀.gpr .r9 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, L⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, L⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbX86_64.pre s₀) :
    APre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r8]; exact BitVec.isLt _

theorem APre.r8' : s₀.gpr .r8 = BitVec.ofNat 64 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.r8, toNat_ofNat hp.lt])

theorem APre.rsi' : s₀.gpr .rsi = BitVec.ofNat 64 R := rsi_ofNat hp.rsi hp.rounds

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hrdi : s.gpr .rdi = St)
    (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdx : s.gpr .rdx = St + BitVec.ofNat 64 272) (hrcx : s.gpr .rcx = Dd)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (hr9 : s.gpr .r9 = S) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩)
    (hstk : (below (s₀.gpr .rsp) 16).Disjoint ⟨Dd, 16 * n⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { rdi := hrdi, rdx := hrdx, rcx := hrcx, r8 := hr8, r9 := hr9, rounds := hp.rounds, hn := hn
    rsi := by rw [hrsi]; exact hp.rsi'
    wc := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    stkW := by rw [hsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkD := by rw [hsp]; exact hstk
    stkC := by rw [hsp]; exact hp.stk_st.sub_right c272
    stkS := by rw [hsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapD := hwrap
    wrapS := by have := hp.wS; omega
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .rdx).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .rdx).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .rdx = BitVec.ofNat 64 c := BitVec.eq_of_toNat_eq (by rw [hc, toNat_ofNat hcl])
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r13₁, r14₁, r15₁, rdx₁, rsp₁, zf₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.r9 fun d _ h => hp.inS (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [rdx₁, hdx]) (by rw [zf₁, rdx₁])) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) hL ax₂ (by rw [g₂ _ (by decide), r14₁, hp.r8'])
    (by rw [g₂ _ (by decide), rbx₁, hp.rdi])) fun s₃ ⟨cx₃, dx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c, g₂ r a]
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (L := fOf c L) (by omega)
    (by rw [g _ (by decide) (by decide) (by decide), r13₁, hp.rcx]) dx₃ cx₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega))
    (fun i hi => by
      rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  have g' (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) (d : r ≠ .r10) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a d, g r a b c]
  refine WP.mono (chain1_wp hfL hL (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r13₁, hp.rcx])
    (by rw [h₄.other _ (by decide) (by decide), cx₃])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r14₁, hp.r8'])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), rbx₁, hp.rdi])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r15₁])) fun s₅ h₅ => ?_
  obtain ⟨r13₅, r14₅, r8₅, rdi₅, rsi₅, rdx₅, rcx₅, r9₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r13) (b : r ≠ .r14) : s₅.gpr r = s₁.gpr r := by
    rw [sv₅ r hr a b, g' r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hsp : s₅.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rsp₁]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs rdi₅ (by rw [rsi₅, g' _ (by decide) (by decide) (by decide) (by decide), rbp₁]) rdx₅ rcx₅
      (by rw [r8₅, b1Of, leftOf]) r9₅ hsp hrd hwr (by omega)
      (Offset.disjoint St (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (hp.stk_st.sub_right c288) (by rw [toNat_add_lt St hw (by decide)]; omega)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩,
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbx₁, hp.rdi],
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbp₁],
    r13₅, by rw [r14₅]; rfl, by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), r15₁], hsp, m₀, hrd,
    hwr⟩

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.X86_64 (UpdateImpl bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

/-- A region disjoint from every region of a frame is unchanged. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := bytesAt_frame hf hd hn

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem absorb_wp (v : UpdateImpl) {s₀ : State} (h0 : absorbX86_64.pre s₀) :
    WP isa (absorb v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rcx = D at hp
  generalize s₀.gpr .r9 = S at hp
  generalize (s₀.gpr .r8).toNat = L at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, rbx₅, rbp₅, r13₅, r14₅, r15₅, rsp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ r13₅ r14₅ m₅
  refine WP.seq (WP.mono (upd_call v args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega)
    (by rw [k₆ _ (by simp [calleeSaved]), r14₅])) fun s₇ h₇ => ?_)
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s₅.gpr r := by rw [sv₇ r hr a, k₆ r hr]
  have hsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₅]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [rdi₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rsi₇, k₆ _ (by simp [calleeSaved]), rbp₅])
    (by rw [rdx₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rcx₇, k₆ _ (by simp [calleeSaved]), r13₅]) r8₇
    (by rw [r9₇, k₆ _ (by simp [calleeSaved]), r15₅]) hsp₇ (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide))) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega⟩
  refine WP.seq (WP.mono (upd_call v args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ calleeSaved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  obtain ⟨s₉, run₉, r13₉, r14₉, rdx₉, rcx₉, sv₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D) (a := fOf c L)
    (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega)
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r13₅])
    (by rw [k₈ _ (by simp [calleeSaved]), r12₇])
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r14₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by unfold restOf nbOf leftOf; split <;> omega)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega) r13₉
    (by rw [rdx₉, k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), rbx₅]) rcx₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by unfold restOf nbOf leftOf at hi; split at hi <;> omega))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have r15₁₀ : s₁₀.gpr .r15 = S := by
    rw [h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
      k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r15₅]
  obtain ⟨s₁₁, run₁₁, rbx₁₁, rbp₁₁, r12₁₁, r13₁₁, r14₁₁, r15₁₁, rsp₁₁, m₁₁⟩ := restore_ok s₁₀ r15₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 48⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₅.mem s₆.mem := by
    rw [← rsp₅]; exact h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₆.mem s₈.mem := by
    rw [← hsp₇, ← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 48⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  have hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega
  -- The key, the data and the return address are in none of these.
  have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint St (by omega) (by omega)
  have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.stk_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
  have dRet : ∀ r ∈ K, (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint_below _ (by decide)
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega))
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, F11.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2224) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega) (by omega)
      · exact hp.stk_s.symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := absSaved_read s₀ S
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₁₁, slot 2176 (by decide) (by decide), a₁]
    · rw [rbp₁₁, slot 2184 (by decide) (by decide), a₂]
    · rw [rsp₁₁, h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
        k₈ _ (by simp [calleeSaved]), hsp₇]
    · rw [r12₁₁, slot 2192 (by decide) (by decide), a₃]
    · rw [r13₁₁, slot 2200 (by decide) (by decide), a₄]
    · rw [r14₁₁, slot 2208 (by decide) (by decide), a₅]
    · rw [r15₁₁, slot 2216 (by decide) (by decide), a₆]
  · intro key msg hr hR hcnt hlen
    rw [hp.rdi] at hr ⊢
    rw [hp.rcx, hp.r8]
    rw [hp.r8] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [frame_bytes hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, frame_bytes hf dDat (by omega)]
    have fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [frame_bytes fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
          (by decide),
        frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      frame_bytes fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Offset.sub_base S (by decide)))
          (by omega)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega)
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · exact (hp.stk_st.sub_right sub).symm
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, frame_bytes f8 dj (by omega), frame_bytes f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega
      have hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega
      have hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.X86_64
