//===-- Serializer.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Serializer.h"

#include "klee/Expr.h"
#include "klee/Solver.h"
#include "klee/Constraints.h"
#include "klee/util/Bits.h"

#include "ConstantDivision.h"
#include "SolverStats.h"

#include "llvm/Support/CommandLine.h"

#include <cstdio>

#include <algorithm> // max, min
#include <cassert>
#include <map>
#include <sstream>
#include <vector>

//remove
#include <iostream>

using namespace klee;

/***/

uint32_t Serializer::getInitialArray(const Array *root, capnp::Orphanage& orphanage) {
  
  assert(root);
  uint32_t arrayId;
//  bool cached = arrayCache.lookupArrayExpr(root, arrayId);
  auto it = arrayCache.find(root->hash());
  
  if(it == arrayCache.end()) {
//  if(!cached) {
    // we make sure the name is unique by including the address.
//    char buf[32];
//    unsigned const addrlen = sprintf(buf, "_%p", (const void*)root) + 1; // +1 for null-termination
//    unsigned const space = (root->name.length() > 32 - addrlen)?(32 - addrlen):root->name.length();
//    memmove(buf + space, buf, addrlen); // moving the address part to the end
//    memcpy(buf, root->name.c_str(), space); // filling out the name part
    
    capnp::Orphan<serialization::Array> arrayOrphan = orphanage.newOrphan<serialization::Array>();
    serialization::Array::Builder array = arrayOrphan.get();
    array.setName(root->name);
    array.setDomain(root->getDomain());
    array.setRange(root->getRange());
    array.setSize(root->size);
    
    if (root->isConstantArray()) {
      capnp::List<uint32_t>::Builder constants = array.initConstantIds(root->size);
      for (unsigned i = 0, e = root->size; i != e; ++i) {
        constants.set(i, serialize(root->constantValues[i], 0, orphanage));
      }
    } else {
      array.setSymbolic();
    }
    
    arrayId = arrayList.size();
    arrayList.push_back(std::move(arrayOrphan));
    
//    arrayCache.hashArrayExpr(root, arrayId);
    arrayCache[root->hash()] = arrayId;
  } else {
    arrayId = it->second; 
  }
  
  return arrayId; 
}

uint32_t Serializer::getArrayForUpdate(const Array *root, 
                                       const UpdateNode *un,
                                       capnp::Orphanage& orphanage) {
  if (!un) {
    return 0;
  } else {
    uint32_t updateNodeId;
//    bool cached = arrayCache.lookupUpdateNodeExpr(un, updateNodeId);
    auto it = updateNodeCache.find(un->hash());
    
    if(it == updateNodeCache.end()){
//    if (!cached) {
      capnp::Orphan<serialization::UpdateNode> updateNodeOrphan = orphanage.newOrphan<serialization::UpdateNode>();
      serialization::UpdateNode::Builder updateNode = updateNodeOrphan.get();
      
      updateNode.setSize(un->getSize());
      updateNode.setIndexExprId(serialize(un->index, 0, orphanage));
      updateNode.setValueExprId(serialize(un->value, 0, orphanage));
      updateNode.setNextNodeId(getArrayForUpdate(root, un->next, orphanage));
      
      updateNodeId = updateNodeList.size();
      updateNodeList.push_back(std::move(updateNodeOrphan));
      
      updateNodeCache[un->hash()] = updateNodeId;
    } else {
      updateNodeId = it->second;
    }
    
    return updateNodeId;
  }
}

capnp::MessageBuilder&& Serializer::serialize(const Query& queryExpr, const std::vector<const Array*>& objects, capnp::MessageBuilder&& message){
  serialization::Query::Builder query = message.initRoot<serialization::Query>();
  capnp::Orphanage orphanage = message.getOrphanage();
  
  // We need this placeholder because update nodes form a linked list by containing pointers to the next 
  // node and we need a way to mark the final node (it will contain a pointer to this dummy)
  capnp::Orphan<serialization::UpdateNode> dummyUpdateNodeOrphan = orphanage.newOrphan<serialization::UpdateNode>();
  serialization::UpdateNode::Builder dummyUpdateNode = dummyUpdateNodeOrphan.get();
  dummyUpdateNode.setSize(0);
  dummyUpdateNode.setIndexExprId(0);
  dummyUpdateNode.setValueExprId(0);
  dummyUpdateNode.setNextNodeId(0);
  updateNodeList.push_back(std::move(dummyUpdateNodeOrphan));
  
  //std::cerr << "\nConstraints: " << queryExpr.constraints.size() << "\n";
  //std::cerr << "Expr: " << queryExpr.expr->getKind() << "\n";
  capnp::List<uint32_t>::Builder constraints = query.initConstraints(queryExpr.constraints.size());
  int i = 0;
  for (ConstraintManager::const_iterator it = queryExpr.constraints.begin(), ie = queryExpr.constraints.end(); it != ie; ++it){
    constraints.set(i, serialize(*it, 0, orphanage));
    ++i;
  }
  
  query.setExpression(serialize(Expr::createIsZero(queryExpr.expr), 0, orphanage));
  
  if(objects.empty()){
    query.setSatUnsat();
  } else {
    capnp::List<uint32_t>::Builder counterExList = query.initCounterExArrayIds(objects.size());
    i = 0;
    for(std::vector<const Array*>::const_iterator it = objects.begin(), ie = objects.end(); it != ie; ++it){
      uint32_t idx = getInitialArray(*it, orphanage);
      counterExList.set(i, idx);
      ++i;
    }
  }
  
  serialization::Query::Data::Builder queryData = query.getData();
  
  capnp::List<serialization::Expr>::Builder exprData = queryData.initExprList(exprList.size());
  i = 0;
  for (std::vector<ExprSz>::iterator it = exprList.begin(), ie = exprList.end(); it != ie; ++it){
    exprData.adoptWithCaveats(i, std::move(*it));
    ++i;
  }
  
  capnp::List<serialization::Array>::Builder arrayData = queryData.initArrayList(arrayList.size());
  i = 0;
  for (std::vector<ArraySz>::iterator it = arrayList.begin(), ie = arrayList.end(); it != ie; ++it){
    arrayData.adoptWithCaveats(i, std::move(*it));
    ++i;
  }
  
  capnp::List<serialization::UpdateNode>::Builder updateNodeData = queryData.initUpdateNodeList(updateNodeList.size());
  i = 0;
  for (std::vector<UpdateNodeSz>::iterator it = updateNodeList.begin(), ie = updateNodeList.end(); it != ie; ++it){
    updateNodeData.adoptWithCaveats(i, std::move(*it));
    ++i;
  }
  
  exprList.clear();
  arrayList.clear();
  updateNodeList.clear();
  
  exprCache.clear();
  arrayCache.clear();
  updateNodeCache.clear();
  
  return std::move(message);
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
uint32_t Serializer::serialize(ref<Expr> e, int *width_out, capnp::Orphanage& orphanage, bool secretSwitch) {
  if (isa<ConstantExpr>(e)) {
    assert(e->getKind() == Expr::Kind::Constant && "Expression is not a constant");
    return serializeActual(e, width_out, orphanage);
  } else {
    auto it = exprCache.find(e->hash());
    if (it != exprCache.end()) {
      if (width_out)
        *width_out = it->second.second;
      return it->second.first;
    } else {
      int width;
      if (!width_out) width_out = &width;
      uint32_t res = serializeActual(e, width_out, orphanage);
      exprCache.insert(std::make_pair(e->hash(), std::make_pair(res, *width_out)));
      return res;
    }
  }
}

uint32_t Serializer::serializeCastExpr(ref<Expr> e, serialization::Expr::Kind kind, int *width_out, capnp::Orphanage& orphanage){
  CastExpr* ce = cast<CastExpr>(e);
  
  capnp::Orphan<serialization::Expr> castOrphan = orphanage.newOrphan<serialization::Expr>();
  serialization::Expr::Builder castExpr = castOrphan.get();
  
  castExpr.setKind(kind);
  castExpr.setWidth(ce->getWidth());
  serialization::Expr::NonConstantExpr::Builder nonConst = castExpr.initNonConstantExpr();
  nonConst.setOtherNonConst();
  capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(ce->getNumKids());

  //std::cerr << "SExt " << ce->src->getKind() << " " << ce->src->getWidth() << "\n";
  kids.set(0, serialize(ce->src, 0, orphanage, true));
  //std::cerr << "After serialize\n";
  
  *width_out = ce->getWidth();

  uint32_t ret = exprList.size();
  exprList.push_back(std::move(castOrphan));
  
  return ret;
}

template<typename T>
uint32_t Serializer::serializeBinaryExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, bool onlyBoolWidthOut, capnp::Orphanage& orphanage){
  T* ae = cast<T>(e);
  
  capnp::Orphan<serialization::Expr> binaryOrphan = orphanage.newOrphan<serialization::Expr>();
  serialization::Expr::Builder binary = binaryOrphan.get();
  
  binary.setKind(kind);
  binary.setWidth(ae->getWidth());
  serialization::Expr::NonConstantExpr::Builder nonConst = binary.initNonConstantExpr();
  nonConst.setOtherNonConst();
  capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(ae->getNumKids());
  
  //std::cerr << "Binary: " << ae->left->getKind() << " " << ae->right->getKind() << "\n";
  
  kids.set(0, serialize(ae->left, width_out, orphanage));
  kids.set(1, serialize(ae->right, width_out, orphanage));
  
  if(onlyBoolWidthOut)
    assert(*width_out!=1 && "uncanonicalized binary expression");
  
  uint32_t ret = exprList.size();
  exprList.push_back(std::move(binaryOrphan));
  
  return ret;
}

template<typename T>
uint32_t Serializer::serializeShiftExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, capnp::Orphanage& orphanage){
  T* ae = cast<T>(e);
  
  capnp::Orphan<serialization::Expr> shiftOrphan = orphanage.newOrphan<serialization::Expr>();
  serialization::Expr::Builder shift = shiftOrphan.get();
  
  shift.setKind(kind);
  shift.setWidth(ae->getWidth());
  serialization::Expr::NonConstantExpr::Builder nonConst = shift.initNonConstantExpr();
  nonConst.setOtherNonConst();
  capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(ae->getNumKids());
  kids.set(0, serialize(ae->left, width_out, orphanage));
  int shiftWidth;
  kids.set(1, serialize(ae->right, &shiftWidth, orphanage));
  
  assert(*width_out!=1 && "uncanonicalized shift expression");
  
  uint32_t ret = exprList.size();
  exprList.push_back(std::move(shiftOrphan));
  
  return ret;
}

template<typename T>
uint32_t Serializer::serializeCmpExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, bool onlyBoolWidthOut, capnp::Orphanage& orphanage){
  T* ae = cast<T>(e);
  
  capnp::Orphan<serialization::Expr> cmpOrphan = orphanage.newOrphan<serialization::Expr>();
  serialization::Expr::Builder cmp = cmpOrphan.get();
  
  cmp.setKind(kind);
  cmp.setWidth(ae->getWidth());
  serialization::Expr::NonConstantExpr::Builder nonConst = cmp.initNonConstantExpr();
  nonConst.setOtherNonConst();
  capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(ae->getNumKids());
  kids.set(0, serialize(ae->left, width_out, orphanage));
  kids.set(1, serialize(ae->right, width_out, orphanage));
  
  if(onlyBoolWidthOut)
    assert(*width_out!=1 && "uncanonicalized comparison expression");
  
  *width_out = 1;
  
  uint32_t ret = exprList.size();
  exprList.push_back(std::move(cmpOrphan));
  
  return ret;
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
uint32_t Serializer::serializeActual(ref<Expr> e, int *width_out, capnp::Orphanage& orphanage) {
  int width;
  if (!width_out) width_out = &width;

  ++stats::queryConstructs;

  uint32_t ret = 0;
  
  switch (e->getKind()) {
  case Expr::Constant: {
//std::cerr << "Constant" << "\n";
    ConstantExpr* CE = cast<ConstantExpr>(e);
    *width_out = CE->getWidth();

    capnp::Orphan<serialization::Expr> constantOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder constant = constantOrphan.get();
    
    constant.setKind(serialization::Expr::Kind::CONSTANT);
    constant.setWidth(CE->getWidth());

    
//    capnp::Data::Builder constantData = constant.initConstantExpr().initValue(CE->getWidth());
//    CE->toMemory(constantData.begin());    
    const uint64_t* val = CE->getAPValue().getRawData();
    uint32_t numWords = CE->getAPValue().getNumWords();
    if(numWords == 1){
      constant.initConstantExpr().setWord(val[0]);
    } else {
      capnp::List<uint64_t>::Builder words = constant.initConstantExpr().initWords(numWords);
      for(unsigned i = 0; i < numWords; ++i){
        words.set(i, val[i]);
      }
    }
    
    ret = exprList.size();
    exprList.push_back(std::move(constantOrphan));
    
    return ret;
  }
    
  // Special
  case Expr::NotOptimized: {
//std::cerr << "NotOptimized" << "\n";
    NotOptimizedExpr* noe = cast<NotOptimizedExpr>(e);
    
    capnp::Orphan<serialization::Expr> noOptOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder noOpt = noOptOrphan.get();
    
    noOpt.setKind(serialization::Expr::Kind::NOT_OPTIMIZED);
    serialization::Expr::NonConstantExpr::Builder nonConst = noOpt.initNonConstantExpr();
    nonConst.setOtherNonConst();
    capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(noe->getNumKids());
    kids.set(0, serialize(noe->src, width_out, orphanage));
    
    ret = exprList.size();
    exprList.push_back(std::move(noOptOrphan));
    
    return ret;
  }

  case Expr::Read: {
//std::cerr << "Read" << "\n";
    ReadExpr* re = cast<ReadExpr>(e);
    assert(re && re->updates.root);
    *width_out = re->updates.root->getRange();
    
    capnp::Orphan<serialization::Expr> readOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder read = readOrphan.get();
    
    read.setKind(serialization::Expr::Kind::READ);
    read.setWidth(*width_out);
    
    serialization::Expr::NonConstantExpr::Builder nonConst = read.initNonConstantExpr();
    capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(re->getNumKids());
    kids.set(0, serialize(re->index, 0, orphanage));
    
    serialization::UpdateList::Builder ul = nonConst.initReadExpr().initUpdateList();
    ul.setArray(getInitialArray(re->updates.root, orphanage));
    ul.setHeadNodeId(getArrayForUpdate(re->updates.root, re->updates.head, orphanage));
    
    ret = exprList.size();
    exprList.push_back(std::move(readOrphan));
    
    return ret;
  }
    
  case Expr::Select: {
//std::cerr << "Select" << "\n";
    SelectExpr* se = cast<SelectExpr>(e);
    
    capnp::Orphan<serialization::Expr> selectOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder select = selectOrphan.get();
    
    select.setKind(serialization::Expr::Kind::SELECT);
    serialization::Expr::NonConstantExpr::Builder nonConst = select.initNonConstantExpr();
    nonConst.setOtherNonConst();
    capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(se->getNumKids());
    kids.set(0, serialize(se->cond, 0, orphanage));
    kids.set(1, serialize(se->trueExpr, width_out, orphanage));
    kids.set(2, serialize(se->falseExpr, width_out, orphanage));
    
    ret = exprList.size();
    exprList.push_back(std::move(selectOrphan));
    
    return ret;
  }

  case Expr::Concat: {
//std::cerr << "Concat" << "\n";
    ConcatExpr* ce = cast<ConcatExpr>(e);
    
    capnp::Orphan<serialization::Expr> concatOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder concat = concatOrphan.get();
    
    concat.setKind(serialization::Expr::Kind::CONCAT);
    concat.setWidth(ce->getWidth());
    uint32_t numKids = ce->getNumKids();
    serialization::Expr::NonConstantExpr::Builder nonConst = concat.initNonConstantExpr();
    nonConst.setOtherNonConst();
    capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(numKids);
    
    for(int i = 0; i < numKids; ++i){
        kids.set(i, serialize(ce->getKid(i), 0, orphanage));
    }
    
//    if(numKids > 0){
//      kids.set(numKids-1, serialize(ce->getKid(numKids-1), 0, orphanage));
//      for (int i = numKids - 2; i >= 0; i--) {
//        kids.set(i, serialize(ce->getKid(i), 0, orphanage));
//      }
//    } else {
//      //std::cerr << "WARNING: CONCAT expression with 0 child expressions\n";
//    }
    
    ret = exprList.size();
    exprList.push_back(std::move(concatOrphan));
    
    *width_out = ce->getWidth();
    return ret;
  }

  case Expr::Extract: {
//std::cerr << "Extract" << "\n";
    ExtractExpr* ee = cast<ExtractExpr>(e);
    
    capnp::Orphan<serialization::Expr> extractOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder extract = extractOrphan.get();

    extract.setKind(serialization::Expr::Kind::EXTRACT);
    extract.setWidth(ee->getWidth());
    
    serialization::Expr::NonConstantExpr::Builder nonConst = extract.initNonConstantExpr();
    nonConst.initExtractExpr().setOffset(ee->offset);
    capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(ee->getNumKids());
    kids.set(0, serialize(ee->expr, width_out, orphanage));
    
    ret = exprList.size();
    exprList.push_back(std::move(extractOrphan));
    
    *width_out = ee->getWidth();
    return ret;
  }

    // Casting

  case Expr::ZExt: {
//std::cerr << "ZExt" << "\n";
    return serializeCastExpr(e, serialization::Expr::Kind::Z_EXT, width_out, orphanage);
  }

  case Expr::SExt: {
//std::cerr << "SExt" << "\n";
    return serializeCastExpr(e, serialization::Expr::Kind::S_EXT, width_out, orphanage);
  }

    // Arithmetic

  case Expr::Add: {
//std::cerr << "Add" << "\n";
    return serializeBinaryExpr<AddExpr>(e, serialization::Expr::Kind::ADD, width_out, true, orphanage);
  }

  case Expr::Sub: {
//std::cerr << "Sub" << "\n";
    return serializeBinaryExpr<SubExpr>(e, serialization::Expr::Kind::SUB, width_out, true, orphanage);
  } 

  case Expr::Mul: {
//std::cerr << "Mul" << "\n";
    return serializeBinaryExpr<MulExpr>(e, serialization::Expr::Kind::MUL, width_out, true, orphanage);
  }

  case Expr::UDiv: {
//std::cerr << "UDiv" << "\n";
    return serializeBinaryExpr<UDivExpr>(e, serialization::Expr::Kind::U_DIV, width_out, true, orphanage);
  }

  case Expr::SDiv: {
//std::cerr << "SDiv" << "\n";
    return serializeBinaryExpr<SDivExpr>(e, serialization::Expr::Kind::S_DIV, width_out, true, orphanage);
  }

  case Expr::URem: {
//std::cerr << "URem" << "\n";
    return serializeBinaryExpr<URemExpr>(e, serialization::Expr::Kind::U_REM, width_out, true, orphanage);
  }

  case Expr::SRem: {
//std::cerr << "SRem" << "\n";
    return serializeBinaryExpr<SRemExpr>(e, serialization::Expr::Kind::S_REM, width_out, true, orphanage);
  }

    // Bitwise

  case Expr::Not: {
//std::cerr << "Not" << "\n";
    NotExpr *ne = cast<NotExpr>(e);
    
    capnp::Orphan<serialization::Expr> notOrphan = orphanage.newOrphan<serialization::Expr>();
    serialization::Expr::Builder notExpr = notOrphan.get();
    
    notExpr.setKind(serialization::Expr::Kind::NOT);
    serialization::Expr::NonConstantExpr::Builder nonConst = notExpr.initNonConstantExpr();
    nonConst.setOtherNonConst();
    capnp::List<uint32_t>::Builder kids = nonConst.initKidIds(ne->getNumKids());
    kids.set(0, serialize(ne->expr, width_out, orphanage));
    
    ret = exprList.size();
    exprList.push_back(std::move(notOrphan));
    
    return ret;
  }    

  case Expr::And: {
//std::cerr << "And" << "\n";
    return serializeBinaryExpr<AndExpr>(e, serialization::Expr::Kind::AND, width_out, false, orphanage);
  }

  case Expr::Or: {
//std::cerr << "Or" << "\n";
    return serializeBinaryExpr<OrExpr>(e, serialization::Expr::Kind::OR, width_out, false, orphanage);
  }

  case Expr::Xor: {
//std::cerr << "Xor" << "\n";
    return serializeBinaryExpr<XorExpr>(e, serialization::Expr::Kind::XOR, width_out, false, orphanage);
  }

  case Expr::Shl: {
//std::cerr << "Shl" << "\n";
    return serializeShiftExpr<ShlExpr>(e, serialization::Expr::Kind::SHL, width_out, orphanage);
  }

  case Expr::LShr: {
//std::cerr << "LShr" << "\n";
    return serializeShiftExpr<LShrExpr>(e, serialization::Expr::Kind::L_SHR, width_out, orphanage);
  }

  case Expr::AShr: {
//std::cerr << "AShr" << "\n";
    return serializeShiftExpr<AShrExpr>(e, serialization::Expr::Kind::A_SHR, width_out, orphanage);
  }

    // Comparison

  case Expr::Eq: {
//std::cerr << "Eq" << "\n";
    return serializeCmpExpr<EqExpr>(e, serialization::Expr::Kind::EQ, width_out, false, orphanage);
  }

  case Expr::Ult: {
//std::cerr << "Ult" << "\n";
    return serializeCmpExpr<UltExpr>(e, serialization::Expr::Kind::ULT, width_out, true, orphanage);
  }

  case Expr::Ule: {
//std::cerr << "Ule" << "\n";
    return serializeCmpExpr<UleExpr>(e, serialization::Expr::Kind::ULE, width_out, true, orphanage);
  }

  case Expr::Slt: {
//std::cerr << "Slt" << "\n";
    return serializeCmpExpr<SltExpr>(e, serialization::Expr::Kind::SLT, width_out, true, orphanage);
  }

  case Expr::Sle: {
//std::cerr << "Sle" << "\n";
    return serializeCmpExpr<SleExpr>(e, serialization::Expr::Kind::SLE, width_out, true, orphanage);
  }

    // unused due to canonicalization
#if 0
  case Expr::Ne:
  case Expr::Ugt:
  case Expr::Uge:
  case Expr::Sgt:
  case Expr::Sge:
#endif

  default: 
    assert(0 && "unhandled Expr type");
    return ret;
  }
}


