module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! CTR tail and tag for scalar contiguous AES-GCM seal. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt padLen zeros)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed)
open Split (SealRegions)

theorem finishScalar_ok (v : GcmImpl) {M : CtxMode} {Ctx W SP S D : Addr} {R n al : Nat}
    {s u : State} {H icb : Block} {a : List Byte}
    (reg : SealRegions M Ctx W SP D S R n n s) (ob : ObPre M Ctx W SP R D n s)
    (post : ObPost Ctx W SP D n s u) (bulk : BlocksResult Ctx W R S D (n/16) s u)
    (hH : blockAt s.mem (Ctx+240#64)=H) (hcb : blockAt s.mem (cbA W)=icb)
    (hal : s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W+16#64+32#64) H (a++zeros (padLen a.length)))
    (slot : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : u.mem.readW (SP+8#64) 64=S) :
    WP isa (Contiguous.finishScalar v.callees) u (BodyPost Ctx W SP S D R n al H icb a s) := by
  unfold Contiguous.finishScalar
  apply WP.seq_assoc
  apply Split.finCallsFrom_ok v reg.lay ob post.rd post.wr reg.sW reg.ks
    reg.sD post.frame post.tlen reg.data.ok.lt post.dat post.len bulk.1 bulk.2.1 bulk.2.2 hH hcb hal habs
  intro rounds len hd
  let off := 16*(n/16)
  let r := n-off
  have le : off≤n := Nat.mul_div_le _ _
  have eq : n-r=off := by dsimp only [r]; omega
  obtain ⟨t,run,ptr,g,mem,rd,wr,_⟩ := tailPtr_ok post.env (by rw [post.rd,post.wr]; exact slot) src
    post.tlen len (Nat.sub_le ..)
  have ptr' : t.gpr .rbx = S+BitVec.ofNat 64 off := by simpa only [eq] using (show t.gpr .rbx=S+BitVec.ofNat 64 (n-r) from ptr)
  have env := post.env.keep (fun z hz => g _ (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> decide)) rd wr
  have r200 := env.perm.wR (show 200+8≤2560 by decide)
  have r208 := env.perm.wR (show 208+8≤2560 by decide)
  obtain ⟨x,run₁,bp,x12,regs,mem₁,rd₁,wr₁⟩ :
      ∃ x, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] t = some x ∧
      x.gpr .rbp=BitVec.ofNat 64 r ∧ x.gpr .r12=D+BitVec.ofNat 64 off ∧
      (∀ z, z≠.r12 → z≠.rbp → x.gpr z=t.gpr z) ∧ x.mem=t.mem ∧ x.rd=t.rd ∧ x.wr=t.wr := by
    refine ⟨_,by xrun [env.r15,r200,r208],?_,?_,?_,?_,?_,?_⟩
    · simpa only [gpr_setReg_self,mem] using len
    · simpa [gpr_setReg,mem,off] using post.dat
    · intro z a b; simp [gpr_setReg,a,b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨x,by rw [runBlock_append,run]; exact run₁,?_⟩)
  have env' := env.keep (fun z hz => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> exact regs _ (by decide) (by decide)) rd₁ wr₁
  have xm := mem₁.trans mem
  have xr := rd₁.trans rd
  have xw := wr₁.trans wr
  have mid : CrMid Ctx (W+16#64) W SP R icb off (D+BitVec.ofNat 64 off) r u.mem 0 x := by
    refine ⟨env',Nat.zero_le _,by simpa using x12,by simpa using bp,hd.of_eq xr xw,by rw [xm]; exact rounds,
      fun hh => by simpa [xm] using hh,fun _ => by simp [bytesAt]; rfl,by rw [xm],.inr (by dsimp [off]; omega),
      by rw [xm]; exact Frame.refl _ _⟩
  have data := ((inputData reg).drop le).of_eq (xr.trans post.rd) (xw.trans post.wr)
  have lay : S+BitVec.ofNat 64 off=D+BitVec.ofNat 64 off ∨
      (⟨S+BitVec.ofNat 64 off,r⟩ : Region).Disjoint ⟨D+BitVec.ofNat 64 off,r⟩ := by
    rcases reg.sD with same|apart
    · exact .inl (by rw [same])
    · exact .inr ((apart.sub_left (Offset.sub_base _ (by dsimp [r]; omega))).sub_right (Offset.sub_base _ (by dsimp [r]; omega)))
  have origin : TailSrc true (W+16#64) W SP x u.mem (D+BitVec.ofNat 64 off) 0 r (S+BitVec.ofNat 64 off) := by
    simp only [TailSrc,↓reduceIte,Nat.sub_zero]
    exact ⟨(regs _ (by decide) (by decide)).trans ptr',data,by simpa using lay,by rw [xm]⟩
  refine (WP.with_rdwr (cryptTailG_ok v reg.lay true mid (by dsimp [off,r]; omega) (by rw [xm]) origin)).mono
    fun t ⟨ho,dr,dw⟩ => ⟨ho,dr.trans xr,dw.trans xw⟩

end VG.Proof.AesGcm.X86_64.ContiguousSeal
