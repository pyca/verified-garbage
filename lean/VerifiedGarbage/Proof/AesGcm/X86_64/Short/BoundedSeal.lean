module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedText
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short

/-! The shared bounded VAES seal authenticates its output after processing the two spans. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Short
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gctr ctxH ctxCiph blockAt inc32 Block)

structure SpanLayout (s : State) (P Q D W SP : Addr) (m n : Nat) : Prop where
  first : m ≤ n
  leftRead : Covers [⟨P,m⟩] (s.rd ++ s.wr)
  leftAlias : P = D ∨ (⟨P,m⟩ : Region).Disjoint ⟨D,n⟩
  leftWork : (⟨P,m⟩ : Region).Disjoint ⟨W,2560⟩
  leftStack : (⟨P,m⟩ : Region).Disjoint (below SP 24)
  rightRead : m < n → Covers [⟨Q,n-m⟩] (s.rd ++ s.wr)
  rightAlias : m < n → Q = D + BitVec.ofNat 64 m ∨ (⟨Q,n-m⟩ : Region).Disjoint ⟨D,n⟩
  rightWork : m < n → (⟨Q,n-m⟩ : Region).Disjoint ⟨W,2560⟩
  rightStack : m < n → (⟨Q,n-m⟩ : Region).Disjoint (below SP 24)

abbrev spanBytes (s : State) (P Q : Addr) (m n : Nat) := bytesAt s.mem P m ++ bytesAt s.mem Q (n-m)

theorem spanBytes_length (s : State) (P Q : Addr) {m n : Nat} (hm : m ≤ n) : (spanBytes s P Q m n).length = n := by
  simp [spanBytes,length_bytesAt, Nat.add_sub_of_le hm]

theorem SpanLayout.original {s t : State} {P Q D W SP : Addr} {m n : Nat} (h : SpanLayout s P Q D W SP m n)
    (hn : n < 2^64) (frame : Frame [⟨W,2560⟩,⟨D,n⟩,below SP 24] s.mem t.mem)
    (dataEq : bytesAt t.mem D n = bytesAt s.mem D n) : spanBytes t P Q m n = spanBytes s P Q m n := by
  have both : bytesAt t.mem D m ++ bytesAt t.mem (D + BitVec.ofNat 64 m) (n-m) =
      bytesAt s.mem D m ++ bytesAt s.mem (D + BitVec.ofNat 64 m) (n-m) := by
    rwa [← bytesAt_add, ← bytesAt_add, Nat.add_sub_of_le h.first]
  have headEq : bytesAt t.mem D m = bytesAt s.mem D m := by
    have eq := congrArg (List.take m) both
    simpa [List.take_append, length_bytesAt, List.take_of_length_le (i := m) (l := bytesAt t.mem D m) (by simp [length_bytesAt]),
      List.take_of_length_le (i := m) (l := bytesAt s.mem D m) (by simp [length_bytesAt])] using eq
  have tailEq : bytesAt t.mem (D + BitVec.ofNat 64 m) (n-m) = bytesAt s.mem (D + BitVec.ofNat 64 m) (n-m) := by
    rw [headEq] at both
    exact List.append_cancel_left both
  have fromFrame {r : Addr} {k : Nat} (hk : k ≤ n) (w : (⟨r,k⟩ : Region).Disjoint ⟨W,2560⟩)
      (d : (⟨r,k⟩ : Region).Disjoint ⟨D,n⟩) (sp : (⟨r,k⟩ : Region).Disjoint (below SP 24)) :
      bytesAt t.mem r k = bytesAt s.mem r k := by
    refine bytesAt_frame frame (fun x hx => ?_) (by omega_using [hk,hn])
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  unfold spanBytes
  congr 1
  · rcases h.leftAlias with rfl|apart
    · exact headEq
    · exact fromFrame h.first h.leftWork apart h.leftStack
  · by_cases eq : m=n
    · simp [eq,bytesAt]
    · have lt := Nat.lt_of_le_of_ne h.first eq
      rcases h.rightAlias lt with rfl|apart
      · exact tailEq
      · exact fromFrame (Nat.sub_le _ _) (h.rightWork lt) apart (h.rightStack lt)

theorem boundedBack {tm : Mem → Mem} {k : Nat} {o s : State} {Ctx W SP Np A D P Q : Addr}
    {nl al n R m : Nat} {J : Block} {tl : BitVec 64}
    (hF : ShortFacts) (hpw : PowFrom powersP ghashP tm o Ctx W SP D n)
    (C : OneCtx o k Ctx W SP Np A D nl al n) (geo : SpanLayout o P Q D W SP m n)
    (hal : al < 512) (hn : n < 512) (small : nb16 al + nb16 n < 32)
    (F : Front tm o Ctx W SP A D R al n J tl (bytesAt o.mem A al) s)
    (left : s.gpr .rbx = P) (right : s.gpr .r12 = Q) (size : s.gpr .rbp = BitVec.ofNat 64 m) :
    WP isa (.seq (.seq (.block textArgs) boundedText) (.seq (sealShort.ghash' ghashP) (.block (tagK 0)))) s
      (SealPostFrom o Ctx W SP D n R al (ctxH o.mem Ctx) J (bytesAt o.mem A al) (spanBytes o P Q m n)) := by
  apply sealBack_parts hF hpw.gh hpw.view C hal hn small boundedText _ (spanBytes_length _ _ _ geo.first) F
  intro t xp mem regs rd wr
  have gs : (⟨textSlot W al n,n⟩ : Region).Sub ⟨W,2560⟩ := by
    unfold textSlot
    apply Lay.wSub
    simp only [grp,nb16] at *
    omega_using [small,hn,hal]
  have span : SpanPair t P Q D (textSlot W al n) m n :=
    ⟨geo.first, (regs _ (by simp)).trans left, (regs _ (by simp)).trans right, (regs _ (by simp)).trans size,
      by rw [rd,wr,F.sm.rd,F.sm.wr]; exact geo.leftRead,
      geo.leftAlias, geo.leftWork.sub_right gs,
      fun lt => by rw [rd,wr,F.sm.rd,F.sm.wr]; exact geo.rightRead lt,
      geo.rightAlias, fun lt => (geo.rightWork lt).sub_right gs⟩
  have hplaintext : spanBytes t P Q m n = spanBytes o P Q m n := by
    change bytesAt t.mem P m ++ bytesAt t.mem Q (n-m) = _
    rw [mem]
    exact geo.original (by omega_using [hn]) F.sm.frame F.dat
  have ks : ∀ b, 16*b < n → blockAt t.mem (W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16*b)) =
      ctxCiph o.mem Ctx R (Nat.repeat inc32 (b+1) J) := by
    intro b hb
    rw [mem, show W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b) =
        W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * (b + 1)) by
      rw [add_ofNat_ofNat, add_ofNat_ofNat, show 1040 + 16 * b = 1024 + 16 * (b + 1) by omega_arith]]
    exact F.ks (b+1) (by simp only [nb16]; omega_using [hb])
  have out := boundedText_ok xp span
  change WP isa boundedText t (TextDone t D (textSlot W al n) (List.zipWith (· ^^^ ·)
    (spanBytes t P Q m n) (bytesAt t.mem (W + BitVec.ofNat 64 1040) n))) at out
  rw [hplaintext, zip_keystream_gctr _ (spanBytes_length _ _ _ geo.first) ks] at out
  exact out

private def boundedFront : Prog isa :=
  .seq powersP (.seq (.block zeroG) (.seq copyA keystream))

theorem bounded_ok (hF : ShortFacts) {tm : Mem → Mem} {k : Nat} {o s : State}
    {Ctx W SP Np A D P Q : Addr} {nl al n m : Nat}
    (C : OneCtx o k Ctx W SP Np A D nl al n) (hpw : PowFrom powersP ghashP tm o Ctx W SP D n)
    (E : OneEntry o Ctx W SP A D n s) (geo : SpanLayout o P Q D W SP m n)
    (hNp : o.gpr .rdx = Np) (hnl' : (o.gpr .rcx).toNat = nl) (hal' : (o.gpr .r9).toNat = al)
    (hnl : nl = 12) (hal : al < 512) (hn : n < 512) (small : nb16 al + nb16 n < 32)
    (left : s.gpr .rbx = P) (right : s.gpr .r11 = Q) (size : s.gpr .r10 = BitVec.ofNat 64 m) :
    WP isa bounded.code s (SealPostFrom o Ctx W SP D n (o.gpr .rsi).toNat al (ctxH o.mem Ctx)
      (Spec.Gcm.j0 (ctxH o.mem Ctx) (bytesAt o.mem Np nl)) (bytesAt o.mem A al) (spanBytes o P Q m n)) := by
  subst hnl
  obtain ⟨tr,u,e,S,aad,dataEq⟩ := shortStart_ok C E hNp hnl' rfl hal' hal hn
  let v := (u.setReg .rbp (u.gpr .r10)).setReg .r12 (u.gpr .r11)
  have kept : ∀ r ∈ [Reg.r13,.r14,.r15,.rsp], v.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> rfl
  have Sv := S.keep (s' := v) C.dE (rs := []) (Frame.refl _ _) (by simp) kept rfl rfl
  have front := front_ok C hpw rfl hal hn small Sv aad dataEq (rest := .block [])
    (fun _ F => WP.block_nil F)
  have p : WP isa boundedFront v (Front tm o Ctx W SP A D (o.gpr .rsi).toNat al n
      (Spec.Gcm.j0 (ctxH o.mem Ctx) (bytesAt o.mem Np 12)) (s.mem.readW (W + BitVec.ofNat 64 224) 64)
      (bytesAt o.mem A al)) := by
    obtain ⟨_,_,fr,F⟩ := front
    cases fr with
    | seq a f => cases f with
      | seq b f => cases f with
        | seq c f => cases f with
          | seq d tailRun => exact ⟨_,_,.seq a (.seq b (.seq c d)), WP.block_nil_iff.mp ⟨_,_,tailRun,F⟩⟩
  obtain ⟨tr',t,e',F⟩ := p
  have rbx : t.gpr .rbx = P := (Exec.gpr_keeps (r := .rbx) (by decide +kernel) e').trans <|
    (Exec.gpr_keeps (r := .rbx) (by decide +kernel) e).trans left
  have r12 : t.gpr .r12 = Q := (Exec.gpr_keeps (r := .r12) (by decide +kernel) e').trans <|
    (Exec.gpr_keeps (r := .r11) (by decide +kernel) e).trans right
  have rbp : t.gpr .rbp = BitVec.ofNat 64 m :=
    (Exec.gpr_keeps (r := .rbp) (by decide +kernel) e').trans <|
    (Exec.gpr_keeps (r := .r10) (by decide +kernel) e).trans size
  have back := boundedBack hF hpw C geo hal hn small F rbx r12 rbp
  unfold bounded sealShort
  refine WP.seq (WP.block_append_iff.mpr ⟨tr, u, e, WP.of_runBlock ⟨v, ?_, ?_⟩⟩)
  · xrun []
  · obtain ⟨_,_,run,post⟩ := back
    cases e' with
    | seq a f => cases f with
      | seq b f => cases f with
        | seq c d => exact ⟨_,_, .seq a (.seq b (.seq c (.seq d run))),post⟩

end VG.Proof.AesGcm.X86_64.Short
