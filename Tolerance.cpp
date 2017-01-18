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
using namespace llvm;

namespace {
  typedef std::map<Value*, Value*> VectorizeMapTable;
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
        else
          errs()<<"Error:"<<*sca <<" has been vectorized.\n";
    }
    bool Findair(Value* sca) {
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
  void PrintMap(VectorizeMap *map)
  {
        errs() <<"(size = "<<map->GetSize()<<")\n";
        VectorizeMapTable::iterator iter;
        for(iter = map->GetBegin();iter!=map->GetEnd();iter++){
            Value* v_sca=iter->first;
            Value* v_vec=iter->second;
            errs() << *v_sca << ": " << *v_vec << "\n";
        }
  }
  Value* GetVecOpValue(IRBuilder<> builder,Value* val,VectorizeMap vec_map){
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
    	//ConstantInt* c_inst=cast<ConstantInt>(val);
		errs()<< "GetVecOpValue Constant:"<<*val <<"\n";
        //create sca alloca and vec alloca, store constant and load into insertelement.
        auto alloca_c = builder.CreateAlloca(val->getType());
        alloca_c->setAlignment(4);
        auto allocaVec = builder.CreateAlloca(VectorType::get(val->getType(), 4),nullptr,"allocaCons");
        //errs()<<"****constant:"<<val->getSplatValue () <<"\n";
        allocaVec->setAlignment(16);
        //errs()<<"****alloca_c:"<<*alloca_c<<"\n";
        auto store_c = builder.CreateStore(val,alloca_c);
        auto load_c = builder.CreateLoad(alloca_c);
        load_c->setAlignment(4);
        //errs()<<"****store_c:"<<*store_c<<"\n";
        //errs()<<"****load_c:"<<*load_c<<"\n";
        Type* load_ty= load_c->getType();
        //errs()<<"****load_ty:"<<*load_ty<<"\n";
        Value* val_c = UndefValue::get(VectorType::get(load_ty, 4));
        //Value *mul_value = ConstantInt::get(val->getType() , *val); 
        for (unsigned i = 0; i < 4; i++)//for 4 copies
        {
			val_c = builder.CreateInsertElement(val_c,load_c, builder.getInt32(i),"insertCons");  
        }
        //errs()<<"****val_c:"<<*val_c<<"\n";
        auto store_val=builder.CreateStore(val_c,allocaVec);
        store_val->setAlignment(4);
        auto load_val=builder.CreateLoad(allocaVec);
        load_val->setAlignment(4);
        return load_val;
        }else {
            errs()<< "Cannot Support Type! "<<*val <<"\n";
        }
      return NULL;
  }

  struct TolerancePass : public FunctionPass {
    static char ID;
    TolerancePass() : FunctionPass(ID) {}
    
    virtual bool runOnFunction(Function &F) {
      errs() << "function name: " << F.getName() << "\n";
      //errs() << "Function body:\n";
      //F.dump();
      VectorizeMap vec_map,check_map,recovery_map,recovery_map1,vec_stored_map;
      std::vector<Value*> binop,loadbefore,CheckPoint;
      static LLVMContext TheContext;
      bool allcheck=false;
      //Dependence pass
      for (auto &B : F) {
       
        for (auto &I : B) {
            errs()<<"=====";
            I.dump();
            errs()<<"=====";
            if (auto *op = dyn_cast<BinaryOperator>(&I)) {
                //add into array
                binop.push_back(op);
            }
            else if (auto *op = dyn_cast<LoadInst>(&I)) {
                //add into array(use before now op)
                loadbefore.push_back(op);
            }
            else if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                Value* lhs = op->getOperand(0);
                Value* rhs = op->getOperand(1);
                errs()<<"*****Find Store:"<<*op<<"\n";
                errs()<<"lhs :"<<*lhs <<"\n";
                errs()<<"rhs:"<<*rhs<<"\n";
                //left op is binop?
                if(isa<BinaryOperator>(*lhs)){
                    if(allcheck){
                        CheckPoint.push_back(op);
                    }else
                    {
                        bool Pflag=false;
                        //find right op uses (alloca inst)
                        for (auto &U : rhs->uses()) {

                           
                            User *user = U.getUser(); 
                            
                            if(isa<LoadInst>(*user)){
                                errs()<<"=Find:"<<*user<<"\n";
                                bool Cflag=true;
                        for(int i=0; i<loadbefore.size(); i++){
                        //if loadinst uses before?
                            if(user==loadbefore[i]){
                                Cflag=false;
                                //errs()<<"@FUCK:"<<*user<<"\n";
                            }
                        }
                        //if find loadinst never use
                        
                        if(Cflag){
                                errs()<<"========\n";
                                errs()<<"BINOP map:\n";
                                //check this load inst uses for binop
                              for(int i=0; i<binop.size(); i++){
                                 errs()<<"binop:"<<*binop[i]<<"\n";
                              
                                errs()<<"loadinst:"<<*user <<"\n";
                                for (auto &U1 : user->uses()) {
                                    User *user1 = U1.getUser(); 
                                    errs()<<"user1:"<<*user1 <<"\n";
                                    
                                    for(int i=0; i<binop.size(); i++){
                                        if(isa<BinaryOperator>(*user1)){
                                        //if binop uses before?
                                            if(user1==binop[i]){
                                                //if difference no check
                                                 errs()<<"====load no uses op!====\n";
                                                Pflag=true;
                                            }else{
                                                 errs()<<"====load uses new op!====\n";
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
                                    errs()<<"Only Find Load before\n";
                                    //only find load before.. but it's useless
                                    Pflag=true;
                                }
                               if(!Pflag){
                                        
                                         break;
                                    }

                            }//find load end

                            }
                            if(Pflag){
                                    errs()<<"Find no binaryop uses load inst\n";
                                    CheckPoint.push_back(op);
                            }
                        }//find sotre inst's left op is binop
                    }//allcheck else end
                }//find store end
            }
        }
      errs()<<"*=*=*CheckPoint:\n";
      for(int i=0; i<CheckPoint.size(); i++)
         errs()<<"CheckPoint:"<<*CheckPoint[i]<<"\n";
      //tolerance

      BasicBlock::iterator ignoreuntilinst;
      /*AllocaInst* recovery_int;
      AllocaInst* recovery_fp;
      bool first_int=false;
      bool first_fp=false;*/
      for (auto &B : F) {
        //errs() << "Basic block:\n";
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
            //errs()<<*scalar_t<<"\n";
            //errs()<<*scalar_t1<<"\n";
            //support inst type?
            
            if(scalar_t->isIntegerTy()){
                
                //errs()<<"Find integer:"<<*scalar_t<<"\n";
	        	auto allocaVec = builder.CreateAlloca(VectorType::get(scalar_t, 4),nullptr,"allocaVec");
                allocaVec->setAlignment(16);
                //errs()<<"address sca:"<<*op<<",vec:"<<*allocaVec<<"\n";
                vec_map.AddPair(op,allocaVec);
                //get vector demo
                auto *vec = vec_map.GetVector(op);
                errs()<< "Tolerance:Create AllocaInst Vectorty:"<<*vec<<"\n";
                /*if(!first_int)
                {
                //Type::getFloatTy(TheContext);
                recovery_int=builder.CreateAlloca(scalar_t,nullptr,"Recovery");
                recovery_int->setAlignment(4);
                first_int=true;
                }*/
                //errs()<<"get vector:"<<*vec<<"\n";
            }  
            if(scalar_t->isFloatTy()){
                auto allocaVec = builder.CreateAlloca(VectorType::get(scalar_t, 4),nullptr,"allocaVec");
                allocaVec->setAlignment(16);
                //errs()<<"address sca:"<<*op<<",vec:"<<*allocaVec<<"\n";
                vec_map.AddPair(op,allocaVec);
                //get vector demo
                auto *vec = vec_map.GetVector(op);
                errs()<< "Tolerance:Create FloatInst Vectorty:"<<*vec<<"\n";
                /*if(!first_fp)
                {
                //Type::getFloatTy(TheContext);
                recovery_fp=builder.CreateAlloca(scalar_t,nullptr,"Recovery");
                recovery_fp->setAlignment(4);
                first_fp=true;
                }*/
            }
            if(scalar_t->isVectorTy()){
                //errs()<<"Find vector:"<<*scalar_t<<"\n";
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
                if(vec_stored_map.Findair(loadinst_ptr)){
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
                //errs()<<"*~Find Load_p:"<<*loadinst_ptr<<"\n";
                errs()<<"Tolerance:Create Vector Element.\n";
                Value* val = UndefValue::get(VectorType::get(load_ty, 4));
                //LoadInst* load_val=builder.CreateLoad(loadinst_ptr);
                //load_val->setAlignment(4);
                for (unsigned i = 0; i < 4; i++)//for 4 copies
                {
                    //errs()<<"*****load_val:"<<*load_val<<"\n";
                    //errs()<<"******:"<<*loadinst_ptr<<"\n";
           			//create insertelement instruction
    				val = builderafter.CreateInsertElement(val,op, builderafter.getInt32(i),"insertElmt");  
                }
                //get vector in map
                auto *vec = vec_map.GetVector(loadinst_ptr);
                //errs()<<"get vector:"<<*vec<<"\n";
                //errs()<<"get insertelement:"<<*val<<"\n";
                //create store into vector
                StoreInst* store_val=builderafter.CreateStore(val,vec);
                store_val->setAlignment(16);
                //errs()<<"create store:"<<*store_val<<"\n";
                }
            }
        }
        //Find operator to neon duplication
        else if (auto *op = dyn_cast<BinaryOperator>(&I)) {
            //errs()<<"Tolerance:Find BinaryOperator\n";
            auto op_name= I.getOpcodeName();
            Type* op_type = op->getType();
            //auto op_name1= op->getOpcode();
            errs()<<"OP Type:"<<*op_type<<"\n";
            errs()<<"-*-*BinaryOperator is:"<<op_name<<"\n";
            // Insert at the point where the instruction `op` appears.
            IRBuilder<> builder(op);
            Value* lhs = op->getOperand(0);
	    	Value* rhs = op->getOperand(1);
            //errs()<<"lhs:"<<*lhs<<"\n";
	    	//errs()<<"rhs:"<<*rhs<<"\n";
            //Value *mul_value = ConstantInt::get(op->getType() , 3); 
            //Value* mul = builder.CreateMul(lhs, mul_value);
            Value* load_val1=GetVecOpValue(builder,lhs,vec_map);
            Value* load_val2=GetVecOpValue(builder,rhs,vec_map);
            Value *vop;
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
            }else if(strcmp(op_name, "sub") == 0){// find op is "fadd"
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateSub(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "mul") == 0){// find op is "fadd"
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateMul(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "sdiv") == 0){// find op is "fadd"
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
            }else if(strcmp(op_name, "fsub") == 0){// find op is "fadd"
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFSub(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "fmul") == 0){// find op is "fadd"
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFMul(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else if(strcmp(op_name, "fdiv") == 0){// find op is "fadd"
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    vop = builder.CreateFDiv(load_val1,load_val2,"Vop");
                    //errs()<<"Create Vop:"<<*vop<<"\n";
                    vec_map.AddPair(op, vop);
                    }else{
                    errs()<<"Error: in Vector operator:"<<*op<<"\n";
                    
                    }
            }else {
                errs()<<"#1 Not Support Operator Type:"<<*op_name<<"\n";
            }

            /**Find Check Point**/
            for (auto &U : op->uses()) {
                User *user = U.getUser();  // A User is anything with operands.
                //Value* v= U.get();
                errs()<<"*****Find:"<<*user<<"\n";
                errs()<<*op<<" - Find Check Point:"<<*user<<"\n";
                Value *rdst = user->getOperand(1);
                auto *vecdst  = vec_map.GetVector(rdst);
                //errs()<<"XXXXXXXXXXXxVOPd:"<<*vop<<"\n";
                //errs()<<"XXXXXXXXXXXxFind:"<<*vecdst<<"\n";
                Value *vecstr = builder.CreateStore(vop,vecdst);
                vec_stored_map.AddPair(rdst,vecdst);//save vec have stored map
                if(isa<StoreInst>(*user)){//Find final store 
                    bool Cflag=false;
                    for(int i=0; i<CheckPoint.size(); i++){
                        //errs()<<"@@@@@@@@@@@@@@@@Nocheck:"<<*CheckPoint[i]<<"\n";
                        //errs()<<"@@@@@@@@@@@@@@@@User:"<<*user<<"\n";
                        if(user==CheckPoint[i]){
                            Cflag=true;
                            //errs()<<"@FUCK:"<<*user<<"\n";
                        }
                    }
        
                    //Value* v= U.get();
                    /*
                    Value *v = user->getOperand(1);
                     errs()<<*user<<" get operands: "<<*user->getOperand(1)<<"\n";
                    for (auto &U1 : v->uses()) {
                        User *user1 = U1.getUser();
                        errs()<<"*****Is Insert?"<<*user1<<"\n";
                    }*/

                //Instruction* op1 = cast<Instruction>(v);
                //if(auto *op1 = dyn_cast<StoreInst>(*user)){//Find final store 
                if(Cflag){
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
                }else {
                errs()<<"#2 Not Support Operator Type:"<<*op_type<<"\n";
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
                auto *ex0=builder.CreateExtractElement(load_vec,lane0,"extractE");
                auto *ex1=builder.CreateExtractElement(load_vec,lane1,"extractE");
                auto *ex2=builder.CreateExtractElement(load_vec,lane2,"extractE");
               
                Instruction* recoveryinst=cast<Instruction>(ex2);
                AllocaInst* recovery=builder.CreateAlloca(recoveryinst->getType(),nullptr,"Recovery");
                recovery->setAlignment(4);
                errs()<<"Recovery:"<<*recovery<<"\n";
                //errs()<<"XXXXXXXXXXX1:\n";
                //errs()<<"XXXXXXXXXXXxOP:"<<*op<<"\n";
                //errs()<<"XXXXXXXXXrecovery:"<<*recovery_fp<<"\n";
                Value *Rval = builder.CreateStore(op, recovery);
                //errs()<<"XXXXXXXXXXX2:\n";
                //#3
                Value *vadd,*vadd1,*fault_check;
                if(op_type->isIntegerTy()){
                vadd = builder.CreateAdd(ex0,ex1,"sum");
                vadd1 = builder.CreateAdd(vadd ,ex2,"sum");
                fault_check=builderafter.CreateICmpNE(vadd1,mul,"Fcmp");
                //Value *Rval = builder.CreateStore(op, recovery_int);
                //recovery_map1.AddPair(user,recovery_int);
                //errs()<<"add"<<*vadd<<"\n";
                }else if(op_type->isFloatTy()){
                vadd = builder.CreateFAdd(ex0,ex1,"sum");
                vadd1 = builder.CreateFAdd(vadd ,ex2,"sum");
                //errs()<<"Fadd"<<*vadd<<"\n";
                fault_check=builderafter.CreateFCmpUNE(vadd1,mul,"Fcmp");
                //Value *Rval = builder.CreateStore(op, recovery_fp);
                //recovery_map1.AddPair(user,recovery_fp);
                }else {
                errs()<<"#3 Not Support Operator Type:"<<*op_type<<"\n";
                }
                //chech create after mutltiple 3
               
                //errs()<<"CMP"<<*fault_check<<"\n";
                //errs()<<"****"<<*user<<"\n";
                check_map.AddPair(user,fault_check);
                check_map.AddPair(fault_check,ex0);
                recovery_map.AddPair(user,op);
                recovery_map1.AddPair(user,recovery);

                //TerminatorInst *ThenTerm = nullptr, *ElseTerm = nullptr;
                //BasicBlock::iterator it(op1);

                //TerminatorInst *ThenTerm , *ElseTerm ;

                //SplitBlockAndInsertIfThenElse(fault_check, op1, &ThenTerm, &ElseTerm,nullptr);
                //builderafter.SetInsertPoint(ThenTerm);

                //builderafter.SetInsertPoint(ElseTerm);
                //user->setOperand(U.getOperandNo(), mul);//final store
                }//Cflag end
            }
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
        
     //Delete map value after insert successfully
      for(int i =0 ; i<recovery_map1.GetSize(); i++){
        errs()<<"Recovery Map:\n";
         //PrintMap(&recovery_map);
         errs()<<"Start Insert Check!\n";
         
            bool check_flag=0;
            for (auto &B : F) {
                //errs()<<"----------\n";
                //B.dump();
               // errs()<<"----------\n";
                for (auto &I : B) {
                    //insert check before store
                    if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                       errs()<<*op<<"\n";
                       if(recovery_map.IsAdded(op)){
                            
                            //errs()<<"Insert check!\n";
                             //errs()<<*op<<"\n";
                             
                            
                          
                            IRBuilder<> builder(op);
                            Value *fault_check = check_map.GetVector(op);
                            Value *recovery = recovery_map1.GetVector(op);
                            errs()<<"OP:"<<*op<<"\n";
                            errs()<<"fault_check"<<*fault_check<<"\n";  
                            Value *ex0 = check_map.GetVector(fault_check);
                            Instruction* faultinst=cast<Instruction>(fault_check);
                            Value* lhs = faultinst->getOperand(0);
                            Value* rhs = faultinst->getOperand(1);
                            Value *recovery_val = recovery_map.GetVector(op);

                            //BinaryOperator* op_inst= cast<BinaryOperator>(recovery_val);
                            Type* op_type =recovery_val ->getType();
                         
                             
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
                            }else {
                            errs()<<"#4 Not Support Operator Type:"<<*op_type<<"\n";
                            }
                            //}
                            //for ( BasicBlock::iterator i = checkTerm->begin(), e = checkTerm->end();i!= e; ++i)
                            //errs()<<"end"<<*checkTerm<<"\n";   
                            //Then = div 3 can recovery
                            TerminatorInst *ThenTerm , *ElseTerm ;
                            SplitBlockAndInsertIfThenElse(cmp_three, checkTerm, &ThenTerm, &ElseTerm,nullptr);
                            IRBuilder<> builderRecovery(ThenTerm);
                            auto* store_recovery=builderRecovery.CreateStore(ex0,recovery);
                            store_recovery->setAlignment(4);
                            //Else = original i
                            IRBuilder<> builderRecoveryElse(ElseTerm);                           
                            
                            auto* store_recoveryElse=builderRecoveryElse.CreateStore(recovery_val,recovery);
                            store_recoveryElse->setAlignment(4);
                            
                            check_flag=1;
                           
                            errs()<<"Delete Map!\n";
                            recovery_map.DeleteVal(op);
                            ////user->setOperand(U.getOperandNo(), mul);//final store
                           
                        }
                    }
                    
                    if(check_flag)
                       break;
                    }
                    
                if(check_flag)
                break;
            }
      }
      //replace recovery value to store
      
     for (auto &B : F) {
                //B.dump();
                for (auto &I : B) {
                    //insert check before store
                    if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                        if(check_map.IsAdded(op)){
                            Value *recovery = recovery_map1.GetVector(op);
                            IRBuilder<> builder(op);
                            auto* load_recovery=builder.CreateLoad(recovery);
                            load_recovery->setAlignment(4);
                            op->setOperand(0, load_recovery);
                        }
                    }
                }
            }
      errs()<<"Show LLVM IR:\n";
      
      for (auto &B : F) {
            B.dump();
            for (auto &I : B) {
              //I.dump();
          }
        }
        
      errs()<<"Vector Map:\n";
      PrintMap(&vec_map);
      errs()<<"Check Map:\n";
      PrintMap(&check_map);
      //errs()<<"Recovery Map:\n";
      //PrintMap(&recovery_map);
      errs()<<"Recovery Map1:\n";
      PrintMap(&recovery_map1);
    
      //PrintMap(&check_map);
      return true;
    }
  };
}

/**===================end of VectorizeMap========================/**/
char TolerancePass::ID = 0;
static RegisterPass<TolerancePass> X("tolerance", "Tolerance Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

