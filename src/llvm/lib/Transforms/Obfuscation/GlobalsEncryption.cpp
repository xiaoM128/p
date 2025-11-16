#include "llvm/Transforms/Obfuscation/GlobalsEncryption.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace polaris {
#define KEY_LEN 4
static_assert(KEY_LEN > 0 && KEY_LEN <= 4);
PreservedAnalyses GlobalsEncryption::run(Module &M, ModuleAnalysisManager &AM) {
  process(M);
  return PreservedAnalyses::none();
}
Function *GlobalsEncryption::buildDecryptFunction(Module &M) {
  std::vector<Type *> Params;
  Params.push_back(Type::getInt8Ty(M.getContext())->getPointerTo());
  Params.push_back(Type::getInt8Ty(M.getContext())->getPointerTo());
  Params.push_back(Type::getInt64Ty(M.getContext()));
  Params.push_back(Type::getInt64Ty(M.getContext()));
  FunctionType *FT =
      FunctionType::get(Type::getVoidTy(M.getContext()), Params, false);
  Function *F = Function::Create(FT, GlobalValue::PrivateLinkage,
                                 Twine("__obfu_globalenc_dec"), M);
  BasicBlock *Entry = BasicBlock::Create(M.getContext(), "entry", F);
  BasicBlock *Cmp = BasicBlock::Create(M.getContext(), "cmp", F);
  BasicBlock *Body = BasicBlock::Create(M.getContext(), "body", F);
  BasicBlock *End = BasicBlock::Create(M.getContext(), "end", F);
  Function::arg_iterator Iter = F->arg_begin();
  Value *Data = Iter;
  Value *Key = ++Iter;
  Value *Len = ++Iter;
  Value *KeyLen = ++Iter;
  IRBuilder<> IRB(Entry);
  Value *I = IRB.CreateAlloca(IRB.getInt64Ty());
  IRB.CreateStore(IRB.getInt64(0), I);
  IRB.CreateBr(Cmp);

  IRB.SetInsertPoint(Cmp);

  Value *Cond = IRB.CreateICmpSLT(IRB.CreateLoad(IRB.getInt64Ty(), I), Len);
  IRB.CreateCondBr(Cond, Body, End);

  IRB.SetInsertPoint(Body);
  Value *IV = IRB.CreateLoad(IRB.getInt64Ty(), I);
  Value *KeyByte = IRB.CreateLoad(
      IRB.getInt8Ty(),
      IRB.CreateGEP(IRB.getInt8Ty(), Key, IRB.CreateSRem(IV, KeyLen)));
  Value *DataByte =
      IRB.CreateLoad(IRB.getInt8Ty(), IRB.CreateGEP(IRB.getInt8Ty(), Data, IV));
  Value *DecValue = IRB.CreateXor(KeyByte, DataByte);
  IRB.CreateStore(DecValue, IRB.CreateGEP(IRB.getInt8Ty(), Data, IV));
  IRB.CreateStore(IRB.CreateAdd(IV, IRB.getInt64(1)), I);
  IRB.CreateBr(Cmp);

  IRB.SetInsertPoint(End);
  IRB.CreateRetVoid();
  return F;
}

void GlobalsEncryption::process(Module &M) {
  const DataLayout &DL = M.getDataLayout();
  std::set<GlobalVariable *> GVs;
  
  // 收集符合条件的全局变量
  for (GlobalVariable &GV : M.globals()) {
    if (GV.isConstant() && GV.hasInitializer() &&
        (GV.getValueType()->isIntegerTy() || GV.getValueType()->isArrayTy())) {
      GlobalValue::LinkageTypes LT = GV.getLinkage();
      if (LT == GlobalValue::InternalLinkage ||
          LT == GlobalValue::PrivateLinkage) {
        GVs.insert(&GV);
      }
    }
  }

  Function *DecFunc = buildDecryptFunction(M);
  
  for (GlobalVariable *GV : GVs) {
    // 检查用户是否都是指令
    bool Ok = true;
    std::vector<Instruction *> Insts;
    std::set<Function *> Funcs;
    
    for (auto *U : GV->users()) {
      if (!isa<Instruction>(U)) {
        Ok = false;
        break;
      }
      Instruction *I = cast<Instruction>(U);
      Insts.push_back(I);
      Funcs.insert(I->getFunction());
    }
    
    if (!Ok || Funcs.empty()) {
      continue;
    }

    // 生成随机密钥
    uint32_t K = getRandomNumber();
    Type *Ty = GV->getValueType();
    uint64_t Size = DL.getTypeAllocSize(Ty);
    
    // 加密初始值
    if (Ty->isIntegerTy()) {
      if (auto *CI = dyn_cast<ConstantInt>(GV->getInitializer())) {
        uint64_t V = CI->getZExtValue();
        // 执行异或加密
        uint8_t *Data = reinterpret_cast<uint8_t*>(&V);
        uint8_t *KeyData = reinterpret_cast<uint8_t*>(&K);
        for (uint64_t i = 0; i < Size; i++) {
          Data[i] ^= KeyData[i % KEY_LEN];
        }
        GV->setInitializer(ConstantInt::get(Ty, V));
      }
    } else if (Ty->isArrayTy()) {
      ArrayType *AT = cast<ArrayType>(Ty);
      Type *EleTy = AT->getArrayElementType();
      if (!EleTy->isIntegerTy()) {
        continue;
      }
      
      if (auto *CA = dyn_cast<ConstantDataArray>(GV->getInitializer())) {
        std::vector<uint8_t> DataBytes;
        StringRef Data = CA->getRawDataValues();
        DataBytes.assign(Data.begin(), Data.end());
        
        // 执行异或加密
        uint8_t *KeyData = reinterpret_cast<uint8_t*>(&K);
        for (uint64_t i = 0; i < DataBytes.size(); i++) {
          DataBytes[i] ^= KeyData[i % KEY_LEN];
        }
        
        GV->setInitializer(ConstantDataArray::get(
            M.getContext(), ArrayRef<uint8_t>(DataBytes)));
      }
    } else {
      continue;
    }

    std::map<Function *, Value *> FV;
    
    // 在每个使用函数中创建解密代码
    for (Function *F : Funcs) {
      if (F->isDeclaration()) continue;
      
      IRBuilder<> IRB(&*F->getEntryBlock().getFirstInsertionPt());
      AllocaInst *Copy = IRB.CreateAlloca(Ty);
      Copy->setAlignment(Align(GV->getAlignment()));
      
      // 创建全局变量的副本
      IRB.CreateMemCpy(Copy, MaybeAlign(GV->getAlignment()), 
                       GV, MaybeAlign(GV->getAlignment()), 
                       ConstantInt::get(IRB.getInt64Ty(), Size));
      
      // 创建密钥变量
      AllocaInst *KeyAlloca = IRB.CreateAlloca(IRB.getInt32Ty());
      IRB.CreateStore(IRB.getInt32(K), KeyAlloca);
      
      // 调用解密函数
      IRB.CreateCall(DecFunc, {
          IRB.CreateBitCast(Copy, IRB.getInt8PtrTy()),
          IRB.CreateBitCast(KeyAlloca, IRB.getInt8PtrTy()),
          IRB.getInt64(Size),
          IRB.getInt64(KEY_LEN)
      });
      
      FV[F] = Copy;
    }

    // 替换全局变量的使用
    for (Instruction *I : Insts) {
      Function *F = I->getFunction();
      if (FV.find(F) != FV.end()) {
        I->replaceUsesOfWith(GV, FV[F]);
      }
    }
  }
}
} // namespace polaris
