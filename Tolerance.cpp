#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/LLVMContext.h"
#include <llvm/Support/CommandLine.h>

using namespace llvm;

static cl::opt<bool>
    CheckTRUMP("check-TRUMP", cl::Optional, cl::init(false),
    cl::desc("Using TRUMP to check"));
static cl::opt<bool>
    CheckMajority("check-majority", cl::Optional, cl::init(false),
    cl::desc("Using Majority to check"));

namespace {
  typedef std::map<Value*, Value*> VectorizeMapTable;
  std::vector<Value*> All_check, Real_check;
  int recovery_alloca=0;
  int recovery_inst=0;
  int recovery_check=0;
  int recovery_num=0;
 
/**===================VectorizeMap========================**/
  class VectorizeMap {
    VectorizeMapTable vmap;
    
    public:
    VectorizeMap(): vmap() {}
    bool IsAdded(Value *sca) {
    return vmap.find(sca)!=vmap.end();
    }
    void AddPair(Value* sca, Value* vec) {
    VectorizeMapTable::iterator iter=vmap.find(sca);
        if(iter == vmap.end())//do not find vectorize
      vmap.insert(std::make_pair(sca, vec));
        //else
          //errs()<<"Error:"<<*sca <<" has been vectorized.\n";
    }
    bool Findpair(Value* sca) {
    VectorizeMapTable::iterator iter=vmap.find(sca);
        if(iter == vmap.end())//do not find vectorize
            return false;
        else
            return true;
    }
    Value* GetVector(Value* sca) {
        VectorizeMapTable::iterator iter=vmap.find(sca);
        if(iter != vmap.end())//find vectorize
           return iter->second;
        else
           return NULL;
    }
    VectorizeMapTable::iterator GetBegin() {
        return vmap.begin();
    }
    VectorizeMapTable::iterator GetEnd() {
        return vmap.end();
    }
    int GetSize(){
        return vmap.size();
    }
    void DeleteVal(Value *op){
        vmap.erase(op);
    }
  };
  void PrintMap(VectorizeMap *map) {
        errs() <<"(size = "<<map->GetSize()<<")\n";
        VectorizeMapTable::iterator iter;
        for(iter = map->GetBegin();iter!=map->GetEnd();iter++){
            Value* v_sca=iter->first;
            Value* v_vec=iter->second;
            errs() << *v_sca << ":" << *v_vec << "\n";
        }
  }
 

  Value* CreateSIMDInst(IRBuilder<> builder,Value* load,Type *op_type,char* str){
    Value* val;
    //unsigned size = op_type->getPrimitiveSizeInBits();
    //errs()<<"Integer size:"<<size<<"\n";
    if(op_type->isDoubleTy()){
        val = UndefValue::get(VectorType::get(op_type, 2));
        for (unsigned i = 0; i < 2; i++)//for 4 copies
        {
            val = builder.CreateInsertElement(val,load, builder.getInt32(i),str);  
        }
    }else if (op_type->isIntegerTy()||op_type->isFloatTy()){
        val = UndefValue::get(VectorType::get(op_type, 4));
        for (unsigned i = 0; i < 4; i++)//for 4 copies
        {
            val = builder.CreateInsertElement(val,load, builder.getInt32(i),str);  
        }
    }else {
         errs()<<"Cannot Create this SIMD type"<<*op_type<<"\n";
    }
    return val;
  }
  Value* GetVecOpValue(IRBuilder<> builder,Value* val,VectorizeMap vec_map,Type *op_type){
    if(isa<LoadInst>(val)){//find add inst and 2 op is load, do SIMD "add"
        //errs()<< "****GetVecOpValue Load!\n";
        LoadInst* ld_inst = cast<LoadInst>(val);//value to loadinst
        Value* sca = ld_inst->getPointerOperand();
        //errs()<<"sca:"<<*sca<<"\n";
        Value *alloca_vec = vec_map.GetVector(sca);
        //errs()<<"get vector:"<<*alloca_vec<<"\n";
        //create load before "add"
        LoadInst* load_val=builder.CreateLoad(alloca_vec);
        load_val->setAlignment(16);
        return load_val;
    }else if(isa<BinaryOperator>(val)){
        //errs()<< "****GetVecOpValue BinaryOperator:\n";
        BinaryOperator* bin_inst=cast<BinaryOperator>(val);
        //errs()<<"bin_inst:"<<*bin_inst<<"\n";
        Value *bin_vec = vec_map.GetVector(bin_inst);
        //errs()<<"get vector:"<<*bin_vec<<"\n";
        return bin_vec;
    }else if(isa<Constant>(val)){
          
        Constant* c = dyn_cast<Constant>(val);
        if(op_type->isDoubleTy()){
            return ConstantVector::getSplat(2, c);
        }else if(op_type->isIntegerTy()||op_type->isFloatTy()){
            return ConstantVector::getSplat(4, c);
        }else {  
            errs()<<"Not support this Constant val:"<<*val<<"\n";
        }
        
        
    }else if(isa<CallInst>(val)){
        //errs()<< "Find Call Inst: "<<*val <<"\n";
        Value* CallInst = vec_map.GetVector(val);
        Value* CallInstVec= vec_map.GetVector(CallInst);
        //errs()<< "Alloca: "<<*CallInst <<"\n";
        //errs()<< "Vector: "<<*CallInstVec <<"\n";

        auto store_c = builder.CreateStore(val,CallInst);
        auto load_c = builder.CreateLoad(CallInst);
        load_c->setAlignment(4);
        Type* inst_ty= val->getType();


        Value* val_c = CreateSIMDInst(builder,load_c,inst_ty,"insertCall");

        auto store_val=builder.CreateStore(val_c,CallInstVec);
        store_val->setAlignment(4);
        auto load_val=builder.CreateLoad(CallInstVec);
        load_val->setAlignment(4);
        return load_val;
       
    }else if(isa<CastInst>(val)){
        //errs()<< "Find Cast Inst: "<<*val <<"\n";
        Value* CastInst = vec_map.GetVector(val);
        Value* CastInstVec= vec_map.GetVector(CastInst);
        //errs()<< "Alloca: "<<*CastInst <<"\n";
        //errs()<< "Vector: "<<*CastInstVec <<"\n";

        auto store_c = builder.CreateStore(val,CastInst);
        auto load_c = builder.CreateLoad(CastInst);
        load_c->setAlignment(4);
        Type* inst_ty= val->getType();
        Value* val_c = CreateSIMDInst(builder,load_c,inst_ty,"insertCast");
       
        auto store_val=builder.CreateStore(val_c,CastInstVec);
        store_val->setAlignment(4);
        auto load_val=builder.CreateLoad(CastInstVec);
        load_val->setAlignment(4);
        return load_val;
       
    }else {
        errs()<< "####return else: Transforms Not Support Type: "<<*val <<"\n";
        return NULL;
        }
      return NULL;
  }
  void InsertCheck(Function &F,VectorizeMap check_map, VectorizeMap recovery_map1, VectorizeMap recovery_map){
    for(int i =0 ; i<recovery_map1.GetSize(); i++){
        //errs()<<"Recovery Map:\n";
         //PrintMap(&recovery_map);
        
         //errs()<<"Start Insert Check!\n";
         
            bool check_flag=0;
            for (auto &B : F) {
                //errs()<<"----------\n";
                //B.dump();
               // errs()<<"----------\n";
                for (auto &I : B) {
                    //insert check before store
                    //I.dump();
                    if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                       //errs()<<"FFF:"<<*op<<"\n";
                       if(recovery_map.IsAdded(op)){
                            
                            //errs()<<"Insert check!\n";
                            //errs()<<"@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"<<*op<<"\n";
                             
                            
                          
                            IRBuilder<> builder(op);
                            Value *fault_check = check_map.GetVector(op);
                            Value *recovery = recovery_map1.GetVector(op);
                            //errs()<<"OP:"<<*op<<"\n";
                            //errs()<<"fault_check"<<*fault_check<<"\n";  
                            Value *ex0 = check_map.GetVector(fault_check);
                            Instruction* faultinst=cast<Instruction>(fault_check);
                            Value* lhs = faultinst->getOperand(0);
                            Value* rhs = faultinst->getOperand(1);
                            Value *recovery_val = recovery_map.GetVector(op);

                            //BinaryOperator* op_inst= cast<BinaryOperator>(recovery_val);
                            Type* op_type =recovery_val ->getType();
                         
                            //before:
                            //  Head
                            //  op
                            //  Tail
                            //after:
                            //  Head
                            //  if(fault_check)
                            //      checkTerm
                            //  op
                            //  Tail
                            TerminatorInst* checkTerm = SplitBlockAndInsertIfThen(fault_check, op,false);
                   
                          
                            IRBuilder<> builderCheck(checkTerm);
                            //Taking mul_three value div by ex0, because only Interger can use Rem operator.
                            //Inter use SDIV, Float use FDIV.
                       
                            //#4
                            Value *mod_three,*mul_value,*cmp_three;
                            if(op_type->isIntegerTy()){
                                 
                                mod_three = builderCheck.CreateSDiv(lhs,ex0,"remThree");
                                
                                Instruction* ty= cast<Instruction>(mod_three);
                                mul_value = ConstantInt::get(ty->getType() , 3);
                               
                                //errs()<<"mod_three:"<<*mod_three<<"\n";   
                                //errs()<<"mul_value :"<<*mul_value <<"\n";   
                                //cmp div ex0 = 3
                              
                                cmp_three = builderCheck.CreateICmpNE(mod_three,mul_value,"FcmpThree");
                            }else if(op_type->isFloatTy()){
                                
                                mod_three = builderCheck.CreateFDiv(lhs,ex0,"remThree");
                                
                                Instruction* ty= cast<Instruction>(mod_three);
                                mul_value = ConstantFP::get(ty->getType() , 3);
                               
                                //errs()<<"Fmod_three:"<<*mod_three<<"\n";   
                                //errs()<<"Fmul_value :"<<*mul_value <<"\n";   
                                //cmp div ex0 = 3
                              
                                cmp_three = builderCheck.CreateFCmpUNE(mod_three,mul_value,"FcmpThree");
                                //errs()<<"Fcmp :"<<*cmp_three <<"\n"; 
                            }else if(op_type->isDoubleTy()){
                                
                                mod_three = builderCheck.CreateFDiv(lhs,ex0,"remThree");
                                
                                Instruction* ty= cast<Instruction>(mod_three);
                                mul_value = ConstantFP::get(ty->getType() , 3);
                               
                                //errs()<<"Fmod_three:"<<*mod_three<<"\n";   
                                //errs()<<"Fmul_value :"<<*mul_value <<"\n";   
                                //cmp div ex0 = 3
                              
                                cmp_three = builderCheck.CreateFCmpUNE(mod_three,mul_value,"FcmpThree");
                                //errs()<<"Fcmp :"<<*cmp_three <<"\n"; 
                            }else {
                                errs()<<"####4 Not Support Operator Type:"<<*op_type<<"\n";
                            }
                            //}
                            //for ( BasicBlock::iterator i = checkTerm->begin(), e = checkTerm->end();i!= e; ++i)
                            //errs()<<"end"<<*checkTerm<<"\n";   
                            //Then = div 3 can recovery
                            unsigned size = op_type->getPrimitiveSizeInBits();
                           
                            TerminatorInst *ThenTerm , *ElseTerm ;

                            SplitBlockAndInsertIfThenElse(cmp_three, checkTerm, &ThenTerm, &ElseTerm,nullptr);
                            IRBuilder<> builderRecovery(ThenTerm);
                            auto* store_recovery=builderRecovery.CreateStore(recovery_val,recovery);
                            store_recovery->setAlignment(size/8);
                            //Else = original i
                            IRBuilder<> builderRecoveryElse(ElseTerm);                           
                            
                            auto* store_recoveryElse=builderRecoveryElse.CreateStore(ex0,recovery);
                            store_recoveryElse->setAlignment(size/8);
                            
                            check_flag=1;
                            Real_check.push_back(op);
                            recovery_check++;
                            //errs()<<"Delete Map!\n";
                            recovery_map.DeleteVal(op);
                            ////user->setOperand(U.getOperandNo(), mul);//final store
                           
                        }//if end
                    }//find store end
                    
                    if(check_flag) break;
                    }//Basciblock
                    
                if(check_flag) break;
            }//Function
      }
}
void Test(){
    errs()<<"@@@@@@@@@@@Majority\n";
}
void InsertMajority(Function &F,VectorizeMap check_map, VectorizeMap recovery_map1, VectorizeMap recovery_map){
    for(int i =0 ; i<recovery_map1.GetSize(); i++){
        //errs()<<"Recovery Map:\n";
         //PrintMap(&recovery_map);
        
         //errs()<<"Start Insert Check!\n";
         
            bool check_flag=0;
            for (auto &B : F) {
                //errs()<<"----------\n";
                //B.dump();
               // errs()<<"----------\n";
                for (auto &I : B) {
                    //insert check before store
                    //I.dump();
                    if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                       //errs()<<"FFF:"<<*op<<"\n";
                       if(recovery_map.IsAdded(op)){
                            
                            //errs()<<"Insert check!\n";
                            //errs()<<"@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"<<*op<<"\n";
                             
                            
                          
                            IRBuilder<> builder(op);
                            Value *fault_check = check_map.GetVector(op);
                            Value *recovery = recovery_map1.GetVector(op);
                            //errs()<<"OP:"<<*op<<"\n";
                            //errs()<<"fault_check"<<*fault_check<<"\n";  
                            Value *ex0 = check_map.GetVector(fault_check);
                            Instruction* faultinst=cast<Instruction>(fault_check);
                            Value* lhs = faultinst->getOperand(0);//protected value
                            Value* rhs = faultinst->getOperand(1);//memory address
                            Value *recovery_val = recovery_map.GetVector(op);

                            //BinaryOperator* op_inst= cast<BinaryOperator>(recovery_val);
                            Type* op_type =recovery_val ->getType();
                         
                            //before:
                            //  Head
                            //  op
                            //  Tail
                            //after:
                            //  Head
                            //  if(fault_check)
                            //      checkTerm
                            //  op
                            //  Tail
                            TerminatorInst* checkTerm = SplitBlockAndInsertIfThen(fault_check, op,false);
                   
                          
                            IRBuilder<> builderCheck(checkTerm);
                            //Taking mul_three value div by ex0, because only Interger can use Rem operator.
                            //Inter use SDIV, Float use FDIV.
                       
                            //#4
                            Value *mod_three,*mul_value,*cmp_three;
                            if(op_type->isIntegerTy()){
                                 
                                mod_three = builderCheck.CreateSDiv(lhs,ex0,"remThree");
                                
                                Instruction* ty= cast<Instruction>(mod_three);
                                mul_value = ConstantInt::get(ty->getType() , 3);
                               
                                //errs()<<"mod_three:"<<*mod_three<<"\n";   
                                //errs()<<"mul_value :"<<*mul_value <<"\n";   
                                //cmp div ex0 = 3
                              
                                cmp_three = builderCheck.CreateICmpNE(mod_three,mul_value,"FcmpThree");
                            }else if(op_type->isFloatTy()){
                                
                                mod_three = builderCheck.CreateFDiv(lhs,ex0,"remThree");
                                
                                Instruction* ty= cast<Instruction>(mod_three);
                                mul_value = ConstantFP::get(ty->getType() , 3);
                               
                                //errs()<<"Fmod_three:"<<*mod_three<<"\n";   
                                //errs()<<"Fmul_value :"<<*mul_value <<"\n";   
                                //cmp div ex0 = 3
                              
                                cmp_three = builderCheck.CreateFCmpUNE(mod_three,mul_value,"FcmpThree");
                                //errs()<<"Fcmp :"<<*cmp_three <<"\n"; 
                            }else if(op_type->isDoubleTy()){
                                
                                mod_three = builderCheck.CreateFDiv(lhs,ex0,"remThree");
                                
                                Instruction* ty= cast<Instruction>(mod_three);
                                mul_value = ConstantFP::get(ty->getType() , 3);
                               
                                //errs()<<"Fmod_three:"<<*mod_three<<"\n";   
                                //errs()<<"Fmul_value :"<<*mul_value <<"\n";   
                                //cmp div ex0 = 3
                              
                                cmp_three = builderCheck.CreateFCmpUNE(mod_three,mul_value,"FcmpThree");
                                //errs()<<"Fcmp :"<<*cmp_three <<"\n"; 
                            }else {
                                errs()<<"####4 Not Support Operator Type:"<<*op_type<<"\n";
                            }
                            //}
                            //for ( BasicBlock::iterator i = checkTerm->begin(), e = checkTerm->end();i!= e; ++i)
                            //errs()<<"end"<<*checkTerm<<"\n";   
                            //Then = div 3 can recovery
                            unsigned size = op_type->getPrimitiveSizeInBits();
                           
                            TerminatorInst *ThenTerm , *ElseTerm ;

                            SplitBlockAndInsertIfThenElse(cmp_three, checkTerm, &ThenTerm, &ElseTerm,nullptr);
                            IRBuilder<> builderRecovery(ThenTerm);
                            auto* store_recovery=builderRecovery.CreateStore(recovery_val,recovery);
                            store_recovery->setAlignment(size/8);
                            //Else = original i
                            IRBuilder<> builderRecoveryElse(ElseTerm);                           
                            
                            auto* store_recoveryElse=builderRecoveryElse.CreateStore(ex0,recovery);
                            store_recoveryElse->setAlignment(size/8);
                            
                            check_flag=1;
                            Real_check.push_back(op);
                            recovery_check++;
                            //errs()<<"Delete Map!\n";
                            recovery_map.DeleteVal(op);
                            ////user->setOperand(U.getOperandNo(), mul);//final store
                           
                        }//if end
                    }//find store end
                    
                    if(check_flag) break;
                    }//Basciblock
                    
                if(check_flag) break;
            }//Function
      }
}
  void ReplaceRecoveryVal(Function &F, VectorizeMap r_map){
    for (auto &B : F) {
        //B.dump();
        for (auto &I : B) {
            //insert check before store
            if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                if(r_map.IsAdded(op)){
                    Value *recovery = r_map.GetVector(op);
                    IRBuilder<> builder(op);
                    auto* load_recovery=builder.CreateLoad(recovery,"ReplaceInst");
            
                    auto *rhs = cast<AllocaInst>(op->getOperand(1));
                    Type* op_type = rhs->getAllocatedType();
                    unsigned size = op_type->getPrimitiveSizeInBits();
                    //errs() << "####op_type: " << *op_type << "\n";
                    //errs() << "####size: " << size << "\n";
                    load_recovery->setAlignment(size/8);
                    op->setOperand(0, load_recovery);
                    recovery_num++;
                }
            }
        }
    }
}

  struct TolerancePass : public FunctionPass {
    static char ID;
    TolerancePass() : FunctionPass(ID) {}
    //int basic_num=0;
    virtual bool runOnFunction(Function &F) {
      errs() << "function name: " << F.getName() << "\n";
      //errs() << "Function body:\n";
      //F.dump();
      VectorizeMap vec_map,check_map,recovery_map,recovery_map1,vec_stored_map;
      std::vector<Value*> binop,loadbefore,CheckPoint, RecoveryPoint, Cast_op, Call_op;
      static LLVMContext TheContext;
      //bool allcheck=false;
      //Dependence pass
      for (auto &B : F) {
       
        for (auto &I : B) {
            if (auto *op = dyn_cast<BinaryOperator>(&I)) {
                //handle castinst and callinst
                Value* lhs = op->getOperand(0);
                Value* rhs = op->getOperand(1);
                //errs()<<"lhs:"<<*lhs<<"\n";
                //errs()<<"rhs:"<<*rhs<<"\n";
                //castinst
                if(isa<CastInst>(lhs)){
                    Cast_op.push_back(lhs);
                }
                if(isa<CastInst>(rhs)){
                    Cast_op.push_back(rhs);
                }
                //callinst
                if(isa<CallInst>(lhs)){
                    Call_op.push_back(lhs);
                }
                if(isa<CallInst>(rhs)){
                    Call_op.push_back(rhs);
                }

                //--------------------------------//
                //add into array
                binop.push_back(op);
            }
            else if (auto *op = dyn_cast<LoadInst>(&I)) {
                //add into array(use before now op)
                loadbefore.push_back(op);
            }
            else if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                IRBuilder<> builder(op);
                Value* lhs = op->getOperand(0);
                Value* rhs = op->getOperand(1);
                //()<<"*****Find Store:"<<*op<<"\n";
                //errs()<<"lhs :"<<*lhs <<"\n";
                //errs()<<"rhs:"<<*rhs<<"\n";
                //left op is binop?
                if(isa<BinaryOperator>(*lhs)){

                    //if(allcheck){
                    //   CheckPoint.push_back(op);
                    //}else
                    //{
                        bool Pflag=false;
                        //find right op uses (alloca inst)
                        for (auto &U : rhs->uses()) {

                           
                            User *user = U.getUser(); 
                            
                        if(isa<LoadInst>(*user)){
                            //errs()<<"=Find:"<<*user<<"\n";
                            bool Cflag=true;
                            for(int i=0; i<loadbefore.size(); i++){
                            //if loadinst uses before?
                                if(user==loadbefore[i]){//find load before = already used
                                    Cflag=false;
                                    //errs()<<"@FUCK:"<<*user<<"\n";
                                }
                             }
                        //if find loadinst never use
                        
                            if(Cflag){
                                //errs()<<"========\n";
                                //errs()<<"BINOP map:\n";
                                //check this load inst uses for binop
                              for(int i=0; i<binop.size(); i++){
                                 //errs()<<"binop:"<<*binop[i]<<"\n";
                              
                                //errs()<<"loadinst:"<<*user <<"\n";
                                for (auto &U1 : user->uses()) {
                                    User *user1 = U1.getUser(); 
                                    //errs()<<"user1:"<<*user1 <<"\n";
                                    
                                    for(int i=0; i<binop.size(); i++){
                                        if(isa<BinaryOperator>(*user1)){//Is use to do binop
                                        //if binop uses before?
                                            if(user1==binop[i]){
                                                 //errs()<<"====load no uses op!====\n";
                                                Pflag=true;
                                            }else{
                                                 //errs()<<"====load uses new op!====\n";
                                                Pflag=false;
                                                break;
                                            }
                                        }else{
                                            Pflag=true;
                                        }
                                    }
                                    }
                                    if(!Pflag){
                                        
                                         break;
                                    }

                                }
                                //break;//only find one load never use before
                            }//Cflag end
                                else {
                                    //errs()<<"Only Find Load before\n";
                                    //only find load before.. but it's useless
                                    Pflag=true;
                                }
                                if(!Pflag){
                                        
                                    break;
                                }

                            }//find load end

                            }
                            if(Pflag){
                                    //errs()<<"Find no binaryop uses load inst\n";
                                    CheckPoint.push_back(op);
                                    All_check.push_back(op);
                                    //recovery_inst++;
                                    //create recovery
                                    //AllocaInst* recovery=builder.CreateAlloca(rhs->getType(),nullptr,"Recovery");
                                    //recovery->setAlignment(4);

                            }
                        }//find sotre inst's left op is binop

                    //}//allcheck else end
                }//find store end
            }
        }
      //errs()<<"*=*=*CheckPoint:\n";
      bool Pflag=false;
      //CREATE recovery allocation instruction
      //AND castinst and callinst allocation
      //for(int i=0; i<CheckPoint.size(); i++)
      //   errs()<<"CheckPoint:"<<*CheckPoint[i]<<"\n";

         for (auto &B : F) {
            for (auto &I : B) {
                if (auto *op = dyn_cast<AllocaInst>(&I)) {

                    IRBuilder<> builder(op);
                    for(int i=0; i<CheckPoint.size(); i++){
                        //errs()<<"!!!!!!!!!!!!!!!!!"<<*CheckPoint[i]<<"\n";
                        //Value* lhs = CheckPoint[i]->getOperand(0);
                        
                        Instruction* op1 = cast<Instruction>(CheckPoint[i]);
                        Value* rhs = op1->getOperand(0);
                        //errs()<<"rhs"<<*rhs<<"\n";
                        AllocaInst* recovery=builder.CreateAlloca(rhs->getType(),nullptr,"Recovery");
                        recovery_alloca++;
                        Type* op_type = rhs->getType();
                        unsigned size = op_type->getPrimitiveSizeInBits();
                        recovery->setAlignment(size/8);
                        //errs()<<"!!!!!!!!!!!!!!!!!"<<*recovery<<"\n";
                        RecoveryPoint.push_back(recovery);
                        Pflag=true;
                    }
                    //build castinst allocation inst
                    for(int i=0; i<Cast_op.size(); i++){
                        Instruction* vop = cast<Instruction>(Cast_op[i]);
                        Type* op_type = vop->getType();
                        AllocaInst* castinst=builder.CreateAlloca(op_type,nullptr,"CastInst");
                       
                        unsigned size = op_type->getPrimitiveSizeInBits();
                        castinst->setAlignment(4);
                        //errs()<<"!!!!!!!!!!!!!!!!!"<<*castinst<<"\n";
                       
                        AllocaInst* CastInstVec;
                        if(op_type->isDoubleTy()){
                            CastInstVec = builder.CreateAlloca(VectorType::get(op_type, 2),nullptr,"CastInstVec");
                        }else if(op_type->isIntegerTy()||op_type->isFloatTy()){
                            CastInstVec = builder.CreateAlloca(VectorType::get(op_type, 4),nullptr,"CastInstVec");
                        }else{
                            //errs()<<"Not support this size:"<<size<<"\n";
                            CastInstVec = builder.CreateAlloca(VectorType::get(op_type, 4),nullptr,"CastInstVec");
                            /*if(size==64){
                                CastInstVec = builder.CreateAlloca(VectorType::get(op_type, 2),nullptr,"CastInstVec");
                            }else {
                                CastInstVec = builder.CreateAlloca(VectorType::get(op_type, 4),nullptr,"CastInstVec");
                            }*/
                            
                        }
                       
                        CastInstVec->setAlignment(16);
                        vec_map.AddPair(Cast_op[i],castinst);
                        vec_map.AddPair(castinst,CastInstVec);
                        Pflag=true;
                    }
                     //build callinst allocation inst
                    for(int i=0; i<Call_op.size(); i++){
                        Instruction* vop = cast<Instruction>(Call_op[i]);
                        Type* op_type = vop->getType();
                        AllocaInst* callinst=builder.CreateAlloca(op_type,nullptr,"CallInst");
                        unsigned size = op_type->getPrimitiveSizeInBits();
                        callinst->setAlignment(4);
                        //errs()<<"!!!!!!!!!!!!!!!!!"<<*callinst<<"\n";
                        
                        AllocaInst* CallInstVec;
                        if(op_type->isDoubleTy()){
                            CallInstVec = builder.CreateAlloca(VectorType::get(op_type, 2),nullptr,"CallInstVec");
                        }else if(op_type->isIntegerTy()||op_type->isFloatTy()){
                            CallInstVec = builder.CreateAlloca(VectorType::get(op_type, 4),nullptr,"CallInstVec");
                        }else{
                            //errs()<<"Not support this size:"<<size<<"\n";
                            CallInstVec = builder.CreateAlloca(VectorType::get(op_type, 4),nullptr,"CallInstVec");
                            /*
                            if(size==64){
                                CallInstVec = builder.CreateAlloca(VectorType::get(op_type, 2),nullptr,"CallInstVec");
                            }else {
                                CallInstVec = builder.CreateAlloca(VectorType::get(op_type, 4),nullptr,"CallInstVec");
                            }*/
                            
                        }
                      
                        CallInstVec->setAlignment(16);
                        vec_map.AddPair(Call_op[i],callinst);
                        vec_map.AddPair(callinst,CallInstVec);
                        Pflag=true;
                    }
                }
                if(Pflag)break;
                                    
            }
            if(Pflag)break;
         }
      //tolerance
      BasicBlock::iterator ignoreuntilinst;

      for (auto &B : F) {
        //errs() << "@@@@Basic block:";
        //B.dump();
        bool BuilderAfterflag=1;
        for (auto &I : B) {
        //BasicBlock* bb=I.getParent();
        //Find allocation instruction
            //I.dump();
        if (BuilderAfterflag) {
        if (auto *op = dyn_cast<AllocaInst>(&I)) {
            //errs()<< "Tolerance:Find AllocaInst!\n";
            
            IRBuilder<> builder(op);
            
            Type* scalar_t= op->getAllocatedType();//not pointer
            
            //Type* scalar_t1= op->getType();//pointer
            
            //errs()<<*scalar_t1<<"\n";
            //support inst type?
            if(scalar_t->isIntegerTy()){//32bits --> [Integer,Integer,Integer,Integer]
             
                auto allocaVec = builder.CreateAlloca(VectorType::get(scalar_t, 4),nullptr,"allocaVec");
                allocaVec->setAlignment(16);
                //errs()<<"address sca:"<<*op<<",vec:"<<*allocaVec<<"\n";
                vec_map.AddPair(op,allocaVec);
               
                //errs()<<"Find integer:"<<*scalar_t<<"\n";
                
                //get vector demo
                auto *vec = vec_map.GetVector(op);
                //errs()<< "Tolerance:Create AllocaInst VectorTy:"<<*vec<<"\n";
                //errs()<<"get vector:"<<*vec<<"\n";
            }  
            else if(scalar_t->isFloatTy()){//32bits --> [Float,Float,Float,Float]
                auto allocaVec = builder.CreateAlloca(VectorType::get(scalar_t, 4),nullptr,"allocaVec");
                allocaVec->setAlignment(16);
                //errs()<<"address sca:"<<*op<<",vec:"<<*allocaVec<<"\n";
                vec_map.AddPair(op,allocaVec);
                //get vector demo
                auto *vec = vec_map.GetVector(op);
                //errs()<< "Tolerance:Create FloatInst Vectorty:"<<*vec<<"\n";
            }else if(scalar_t->isDoubleTy()){//64bits --> [Double,Double]
                auto allocaVec = builder.CreateAlloca(VectorType::get(scalar_t, 2),nullptr,"allocaVec");
                allocaVec->setAlignment(16);
                //errs()<<"address sca:"<<*op<<",vec:"<<*allocaVec<<"\n";
                vec_map.AddPair(op,allocaVec);
                //get vector demo
                auto *vec = vec_map.GetVector(op);
                //errs()<< "Tolerance:Create FloatInst Vectorty:"<<*vec<<"\n";
            }
        }
        else if (StoreInst *op = dyn_cast<StoreInst>(&I)) {//find store constant to allocainst and store same value to vector
                IRBuilder<> builder(op);
                Value* lhs = op->getOperand(0);
                Value* rhs = op->getOperand(1);
                //()<<"*****Find Store:"<<*op<<"\n";
                
                //left op is binop?
                if(isa<Constant>(lhs)){
                    if(vec_map.Findpair(rhs)){
                        Value *vec = vec_map.GetVector(rhs);
                        Constant* c = dyn_cast<Constant>(lhs);
                        auto alloca_op=cast<AllocaInst>(rhs);
                        Type* op_type = alloca_op->getAllocatedType();;
                        /*errs()<<"lhs :"<<*lhs <<"\n";
                        errs()<<"rhs:"<<*rhs<<"\n";
                        errs()<<"op:"<<op_type->isIntegerTy()<<"\n";*/
                        if(op_type->isDoubleTy()){
                            Value *store_constant = builder.CreateStore(ConstantVector::getSplat(2, c),vec);
                            //errs()<<"Constant Type:"<<*op_type<<"\n";
                        }else if(op_type->isIntegerTy()||op_type->isFloatTy()){
                            Value *store_constant = builder.CreateStore(ConstantVector::getSplat(4, c),vec);
                            //errs()<<"Constant Type:"<<*op_type<<"\n";
                        }else {  
                            //errs()<<"Not support this Constant Type:"<<*op_type<<"\n";
                            errs()<<"Not support this Constant val:"<<*rhs<<"\n";
                        }
                        
                    }
                    
                 
        
                }
        }
        //Find load instruction & create vector before loadinst
        else if (auto *op = dyn_cast<LoadInst>(&I)) {
            bool VecFlag=false;//if load for binop
                //find load is use for binary operator
                for (auto &U : op->uses()) {
                    User *user = U.getUser(); 
                    if(isa<BinaryOperator>(*user)){
                        VecFlag=true;
                    }
                }
            if(VecFlag){
                Value* loadinst_ptr=op->getPointerOperand();
                Type* load_ty= op->getType();
                //Value *load_dst = op->getOperand(0);
                //errs()<<"XXXXXXXXXXXxloadinst_ptr:"<<*loadinst_ptr<<"\n";
                //check if vec have already saved value, if not create insert element
                if(vec_stored_map.Findpair(loadinst_ptr)){
                    auto *vecdst = vec_stored_map.GetVector(loadinst_ptr);
                    //errs()<<"XXXXXXXXXXXxvecdst:"<<*vecdst<<"\n";
                }else
                {
                BuilderAfterflag=0;
                BasicBlock::iterator instIt(I);
                IRBuilder<> builderafter(instIt->getParent(), ++instIt);
                ignoreuntilinst=instIt;
                //errs()<<"*@@@@*set ignore point:"<<*instIt<<"\n";
                //IRBuilder<> builder(op);
                
                //
                //
                /*Type* load_ty1= loadinst_ptr->getType();
                errs()<<"~Load type:"<<*load_ty<<"\n";
                errs()<<"~Load type1:"<<*load_ty1<<"\n";*/
                /*errs()<<"*~Find op:"<<*op<<"\n";
                errs()<<"*~Find Load_p:"<<*loadinst_ptr<<"\n";
                errs()<<"Tolerance:Create Vector Element.\n";
                PrintMap(&vec_map);
                */
                if(vec_map.Findpair(loadinst_ptr)){
                    //##double1
                    //unsigned size = load_ty->getPrimitiveSizeInBits();
                    //errs()<<"Integer size:"<<size<<"\n";
                    Value* val = CreateSIMDInst(builderafter,op,load_ty,"insertElmt");
                   
                
                    //errs()<<"XXXXXXXXXXXxloadinst_ptr:"<<*loadinst_ptr<<"\n";
                    auto *vec = vec_map.GetVector(loadinst_ptr);//original load's alloca inst
                    //errs()<<"XXXXXXXXXXXxvec_ptr:"<<*vec<<"\n";
                    //errs()<<"get vector:"<<*vec<<"\n";
                    //errs()<<"get insertelement:"<<*val<<"\n";
                    //create store into vector
                    StoreInst* store_val=builderafter.CreateStore(val,vec);
                    store_val->setAlignment(16);
                }
                //errs()<<"create store:"<<*store_val<<"\n";
                }
            }
        }/*else if (auto *op = dyn_cast<CastInst>(&I)) {
        }*/
        //Find operator to neon duplication
        else if (auto *op = dyn_cast<BinaryOperator>(&I)) {
            //errs()<<"Tolerance:Find BinaryOperator\n";
            auto op_name= I.getOpcodeName();
            Type* op_type = op->getType();
            //auto op_name1= op->getOpcode();
            //errs()<<"OP:"<<*op<<"\n";
            //errs()<<"OP Type:"<<*op_type<<"\n";
            //errs()<<"-*-*BinaryOperator is:"<<op_name<<"\n";
            // Insert at the point where the instruction `op` appears.
            IRBuilder<> builder(op);
            Value* lhs = op->getOperand(0);
            Value* rhs = op->getOperand(1);
            //errs()<<"lhs:"<<*lhs<<"\n";
            //errs()<<"rhs:"<<*rhs<<"\n";
            //Value *mul_value = ConstantInt::get(op->getType() , 3); 
            //Value* mul = builder.CreateMul(lhs, mul_value);
            Value* load_val1=GetVecOpValue(builder,lhs,vec_map,op_type);
            Value* load_val2=GetVecOpValue(builder,rhs,vec_map,op_type);
            Value *vop;
            //free time, using binaryoperator::create!!
            //#1
            if(strcmp(op_name, "add") == 0){// find op is "add"
            //errs()<<"Find add:"<<op_name<<"\n";
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateAdd(load_val1,load_val2,"Vop");
                    //errs()<<"Create add:"<<*vadd<<"\n";
                    //map add
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    }
            }else if(strcmp(op_name, "sub") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateSub(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "mul") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateMul(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    //errs()<<"original Vop:"<<*op<<"\n";
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "sdiv") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateSDiv(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "fadd") == 0){// find op is "fadd"
            //errs()<<"Find add:"<<op_name<<"\n";
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFAdd(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vadd<<"\n";
                    //map add
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "fsub") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFSub(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "fmul") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFMul(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "fdiv") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFDiv(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "and") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateAnd(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "or") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateOr(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "xor") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateXor(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "shl") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateShl(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "lshr") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateLShr(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "ashr") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateAShr(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "srem") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateSRem(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "urem") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateURem(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "frem") == 0){
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFRem(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else {
                errs()<<"####1 Not Support Operator Type:"<<*op_name<<"\n";
                I.dump();
            }

            /**Find Check Point**/
            //if find store, do vecop's store, and check is checkpoint? then insert mul 3
            //if not, just create vop above
            for (auto &U : op->uses()) {
                User *user = U.getUser();  // A User is anything with operands.
                //Value* v= U.get();
                //errs()<<"*****Find:"<<*user<<"\n";
                //errs()<<*op<<" - Find Check Point:"<<*user<<"\n";

                int recovery_count=0;
                if(isa<StoreInst>(*user)){//Find final store 
                    bool Cflag=false;
                    Value *rdst = user->getOperand(1);
                    //errs()<<"XXXXXXXXXXXxrdst:"<<*rdst<<"\n";
                    Value *vecdst;
                    /*if(isa<GetElementPtrInst>(rdst)){
                        errs()<<"XXXXXXXXXXXGetElementPtrInst:"<<*rdst<<"\n";
                        GetElementPtrInst* rinst=cast<GetElementPtrInst>(rdst);
                        Type* scalar_t= rinst->getSourceElementType();//not pointer
                        createAllocaVec(builder,rdst,vec_map, scalar_t);
                    }*/
                    if(vec_map.IsAdded(rdst)){
                        vecdst  = vec_map.GetVector(rdst);  
                        //errs()<<"XXXXXXXXXXXxVOPd:"<<*vop<<"\n";
                        //errs()<<"XXXXXXXXXXXxFind:"<<*vecdst<<"\n";
                        Value *vecstr = builder.CreateStore(vop,vecdst);
                        vec_stored_map.AddPair(rdst,vecdst);//save vec have stored map  
                    }

                    for(int i=0; i<CheckPoint.size(); i++){
                       
                        //errs()<<"@@@@@@@@@@@@@@@@Nocheck:"<<*CheckPoint[i]<<"\n";
                        //errs()<<"@@@@@@@@@@@@@@@@User:"<<*user<<"\n";
                        if(user==CheckPoint[i]){

                            Cflag=true;
                            //errs()<<"@FUCK:"<<*user<<"\n";
                            recovery_count=i;//save recovery inst num
                        }
                    }
        
                    //Value* v= U.get();
             

                    //Instruction* op1 = cast<Instruction>(v);
                    //if(auto *op1 = dyn_cast<StoreInst>(*user)){//Find final store 
                    if(Cflag){//check is need
                        BasicBlock::iterator instIt(I);
                        IRBuilder<> builderafter(instIt->getParent(), ++instIt);
                        //errs()<<"*@@@@*Set ignore point:"<<*instIt<<"\n";
                        ignoreuntilinst=instIt;
                        BuilderAfterflag=0;
                        //#2
                        Value *mul,*mul_value;
                        if(op_type->isIntegerTy()){
                            mul_value = ConstantInt::get(op->getType() , 3); 
                            mul = builderafter.CreateMul(op, mul_value,"Fmul");
                            //errs()<<"mul"<<*mul<<"\n";
                        }else if(op_type->isFloatTy()){
                            mul_value = ConstantFP::get(op->getType() , 3.0); 
                            mul = builderafter.CreateFMul(op, mul_value,"Fmul");
                            //errs()<<"Fmul"<<*mul<<"\n";
                        }else if(op_type->isDoubleTy()){
                            mul_value = ConstantFP::get(op->getType() , 3.0); 
                            mul = builderafter.CreateFMul(op, mul_value,"Fmul");
                            //errs()<<"Fmul"<<*mul<<"\n";
                        }else {
                            errs()<<"####2 Not Support Operator Type:"<<*op_type<<"\n";
                        }
                        //create load vector
                        //Value* final_store=user->getOperand(1);
                        //errs()<<"*XXXXX*:"<<*user->getOperand(1)<<"\n";
                        //auto *vec = vec_map.GetVector(final_store);
                        //auto *op_vec = vec_map.GetVector(op);
                        //create final store vector
                        //auto* store_vec=builder.CreateStore(op_vec,vec);
                        auto* load_vec=builder.CreateLoad(vecdst);//before is ok
                        load_vec->setAlignment(4);
                        
                        //create sum of three copies
                        uint64_t lane0= 0;
                        uint64_t lane1= 1;
                        uint64_t lane2= 2;
                        Value *ex0;
                        Value *ex1;
                        Value *ex2;
                        //unsigned size = op_type->getPrimitiveSizeInBits();
                        //errs()<<"Integer size:"<<size<<"\n";
                       
                        //#2.5 float --> three element, double --> two element
                        if(op_type->isDoubleTy()){
                            ex0=builder.CreateExtractElement(load_vec,lane0,"extractE");
                            ex1=builder.CreateExtractElement(load_vec,lane1,"extractE");
                        }else if(op_type->isIntegerTy()||op_type->isFloatTy()){
                            ex0=builder.CreateExtractElement(load_vec,lane0,"extractE");
                            ex1=builder.CreateExtractElement(load_vec,lane1,"extractE");
                            ex2=builder.CreateExtractElement(load_vec,lane2,"extractE");
                        }else {
                            errs()<<"####2.5 Not Support Operator Type:"<<*op_type<<"\n";
                        }
                        
                        
                        //Instruction* recoveryinst=cast<Instruction>(ex2);
                        //AllocaInst* recovery=builder.CreateAlloca(recoveryinst->getType(),nullptr,"Recovery");
                        //recovery->setAlignment(4);
                        //errs()<<"Recovery:"<<*recovery<<"\n";
                        //save true value to recovery if no fault occur
                        //errs()<<"##########################"<<*op<<"\n";
                        //errs()<<"1##########################"<<*RecoveryPoint[recovery_count]<<"\n";
                        Value *Rval = builderafter.CreateStore(op, RecoveryPoint[recovery_count]);
                        //errs()<<"2##########################\n";
                        //#3
                        Value *vadd,*vadd1,*fault_check;
                        if(op_type->isIntegerTy()){
                            vadd = builder.CreateAdd(ex0,ex1,"sum");
                            vadd1 = builder.CreateAdd(vadd ,ex2,"sum");
                            fault_check=builderafter.CreateICmpNE(vadd1,mul,"Fcmp");
                           
                        //errs()<<"add"<<*vadd<<"\n";
                        }else if(op_type->isFloatTy()){
                            vadd = builder.CreateFAdd(ex0,ex1,"sum");
                            vadd1 = builder.CreateFAdd(vadd ,ex2,"sum");
                            //errs()<<"Fadd"<<*vadd<<"\n";
                            fault_check=builderafter.CreateFCmpUNE(vadd1,mul,"Fcmp");
                        }else if(op_type->isDoubleTy()){
                            vadd = builder.CreateFAdd(ex0,ex1,"sum");
                            vadd1 = builder.CreateFAdd(vadd ,ex1,"sum");//ex1 add double times
                            //errs()<<"Fadd"<<*vadd<<"\n";
                            fault_check=builderafter.CreateFCmpUNE(vadd1,mul,"Fcmp");
                        }else {
                            errs()<<"####3 Not Support Operator Type:"<<*op_type<<"\n";
                        }
                        //chech create after mutltiple 3
                       
                        //errs()<<"CMP"<<*fault_check<<"\n";
                        //errs()<<"****"<<*user<<"\n";
                        check_map.AddPair(user,fault_check);
                        check_map.AddPair(fault_check,ex0);
                        recovery_map.AddPair(user,op);
                        recovery_map1.AddPair(user,RecoveryPoint[recovery_count]);
                        recovery_inst++;
                        //TerminatorInst *ThenTerm = nullptr, *ElseTerm = nullptr;
                        //BasicBlock::iterator it(op1);

                        //TerminatorInst *ThenTerm , *ElseTerm ;

                        //SplitBlockAndInsertIfThenElse(fault_check, op1, &ThenTerm, &ElseTerm,nullptr);
                        //builderafter.SetInsertPoint(ThenTerm);

                        //builderafter.SetInsertPoint(ElseTerm);
                        //user->setOperand(U.getOperandNo(), mul);//final store
                    }//Cflag end

                }//Find final store end
            }
            
          }
        } else{//builder after flag
                //errs()<<"@@@@Ignore instruction:\n";
                //I.dump();
                BasicBlock::iterator instIt(I);
                //errs()<<*<<"\n";
                if(++instIt==ignoreuntilinst){
                    //errs()<<"*@@@@*Reset builderafter at:"<<*instIt<<"\n";
                    BuilderAfterflag=1;
                }
                //BuilderAfterflag=1;
            }
          //I.dump();
 
        }
       
        
        

      }
      //Create Fault Recovery
      //Delete map value after insert successfully
      InsertCheck(F,check_map,recovery_map1,recovery_map);
      
      if(CheckMajority)
      {
        Test();
      }
      //replace recovery value to store
      ReplaceRecoveryVal(F, recovery_map1);
     
      //errs()<<"Show LLVM IR:\n";
      /*
      for (auto &B : F) {
            B.dump();
            for (auto &I : B) {
              //I.dump();
          }
        }
        */
        /*
      errs()<<"Vector Map:\n";
      PrintMap(&vec_map);
      errs()<<"Check Map:\n";
      PrintMap(&check_map);
      errs()<<"Recovery Map:\n";
      PrintMap(&recovery_map);
      errs()<<"Recovery Map1:\n";
      PrintMap(&recovery_map1);
      */
      //errs()<<"check point size:"<<CheckPoint.size()<<"\n";
      /*errs()<<"recovery_alloca:"<<recovery_alloca<<"\n";
      errs()<<"recovery_inst:"<<recovery_inst<<"\n";
      errs()<<"recovery_check:"<<recovery_check<<"\n";
      errs()<<"recovery_num:"<<recovery_num<<"\n";
      errs()<<"All_check:"<<All_check.size()<<"\n";
      for(int i=0; i<All_check.size(); i++) errs()<<i<<": "<<*All_check[i]<<"\n";
      errs()<<"Real_check:"<<Real_check.size()<<"\n";
      for(int i=0; i<Real_check.size(); i++) errs()<<i<<": "<<*Real_check[i]<<"\n";*/
      //PrintMap(&check_map);
      errs()<<"recovery_num:"<<recovery_num<<"\n";
      return true;
    }
  };
}

/**===================end of VectorizeMap========================/**/
char TolerancePass::ID = 0;
static RegisterPass<TolerancePass> X("tolerance", "Tolerance Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);