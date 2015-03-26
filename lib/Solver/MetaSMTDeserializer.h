 /*
 * MetaSMTDeserializer.h
 *
 *  Created on: 15 Mar 2015
 *      Author: rakadjiev
 */

#ifndef METASMTDESERIALIZER_H_
#define METASMTDESERIALIZER_H_


#include "ConstantDivision.h"
#include "SolverStats.h"
#include "klee/util/Bits.h"

#include "Serialization.capnp.h"
#include <capnp/message.h>
#include <capnp/common.h>
#include <kj/array.h>

#include "APInt.h"

#include <unordered_map>

#include <cstdio>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/frontend/Array.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/support/run_algorithm.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Group.hpp>

#define Expr VCExpr
#define STP STP_Backend
#include <metaSMT/backend/STP.hpp>
#undef Expr
#undef STP
 
#include <boost/mpl/vector.hpp>
#include <boost/format.hpp>

#include <capnp/serialize.h>
#include <capnp/serialize-packed.h>
#include <sys/stat.h>
#include <fcntl.h>

#define DIRECT_CONTEXT

namespace klee {

typedef metaSMT::logic::Predicate<proto::terminal<metaSMT::logic::tag::true_tag>::type  > const MetaSMTConstTrue;
typedef metaSMT::logic::Predicate<proto::terminal<metaSMT::logic::tag::false_tag>::type  > const MetaSMTConstFalse;
typedef metaSMT::logic::Array::array MetaSMTArray;

static const bool mimic_stp = true;

template<typename SolverContext>
class MetaSMTDeserializer {
public:

    MetaSMTDeserializer(SolverContext& solver, bool optimizeDivides, bool useConstructCaching) : 
      solver(solver), optimizeDivides(optimizeDivides), useConstructCaching(useConstructCaching), avg(0), cnt(0), max(0) { };
    virtual ~MetaSMTDeserializer() {
      std::cerr << "Cnt: " << cnt << ", Avg: " << avg << ", Max: " << max << "\n";
    };
    
    capnp::MessageBuilder&& deserializeAndSolve(kj::ArrayPtr<const kj::ArrayPtr<const capnp::word>> bytes, capnp::MessageBuilder&& replyMsg);
    
    typename SolverContext::result_type getInitialRead(uint32_t arrayId, uint32_t index);
    typename SolverContext::result_type getArrayForUpdate(uint32_t arrayId, uint32_t updateNodeId);
    typename SolverContext::result_type getInitialArray(uint32_t arrayId);
    MetaSMTArray buildArray(unsigned elem_width, unsigned index_width);
    
    typename SolverContext::result_type getTrue();
    
    typename SolverContext::result_type getFalse();
    
    typename SolverContext::result_type bvOne(unsigned width);
    
    typename SolverContext::result_type bvZero(unsigned width);
    
    typename SolverContext::result_type bvMinusOne(unsigned width);
    
    typename SolverContext::result_type bvConst32(unsigned width, uint32_t value);
    
    typename SolverContext::result_type bvConst64(unsigned width, uint64_t value);
       
    typename SolverContext::result_type bvZExtConst(unsigned width, uint64_t value);    
    typename SolverContext::result_type bvSExtConst(unsigned width, uint64_t value);
    
    //logical left and right shift (not arithmetic)
    typename SolverContext::result_type bvLeftShift(typename SolverContext::result_type expr, unsigned width, unsigned shift, unsigned shiftBits);
    typename SolverContext::result_type bvRightShift(typename SolverContext::result_type expr, unsigned width, unsigned amount, unsigned shiftBits);
    typename SolverContext::result_type bvVarLeftShift(typename SolverContext::result_type expr, typename SolverContext::result_type amount, unsigned width);
    typename SolverContext::result_type bvVarRightShift(typename SolverContext::result_type expr, typename SolverContext::result_type amount, unsigned width);
    typename SolverContext::result_type bvVarArithRightShift(typename SolverContext::result_type expr, typename SolverContext::result_type amount, unsigned width);
        
private:
    SolverContext&  solver;
    bool optimizeDivides;
    bool useConstructCaching;
    
    long double avg;
    int cnt;
    int max;
    
    capnp::List<serialization::Expr>::Reader exprList;
    capnp::List<serialization::Array>::Reader arrayList;
    capnp::List<serialization::UpdateNode>::Reader updateNodeList;
    
    std::unordered_map<uint32_t, std::pair<typename SolverContext::result_type, uint32_t>> exprCache;
    std::unordered_map<uint32_t, typename SolverContext::result_type> arrayCache;
    std::unordered_map<uint32_t, typename SolverContext::result_type> updateNodeCache;
    
    typename SolverContext::result_type deserialize(uint32_t exprId, int *width_out);
    typename SolverContext::result_type deserializeActual(uint32_t exprId, int *width_out);
    
    uint64_t constantToZExtValue(serialization::Expr::Reader constantExpr);
    llvm::APIntLite constantToAPInt(serialization::Expr::Reader constantExpr, int* width_out);
    llvm::APIntLite constantToAPInt(uint64_t value, uint32_t width);
    llvm::APIntLite constantToAPInt(uint64_t* values, uint32_t numWords, uint32_t width);
    template<typename Arg> typename SolverContext::result_type aPIntToMetaSMTConstant(Arg&& val);
    
    typename SolverContext::result_type bvBoolExtract(typename SolverContext::result_type expr, int bit);
    typename SolverContext::result_type bvExtract(typename SolverContext::result_type expr, unsigned top, unsigned bottom);
    typename SolverContext::result_type eqExpr(typename SolverContext::result_type a, typename SolverContext::result_type b);
    
    typename SolverContext::result_type constructAShrByConstant(typename SolverContext::result_type expr, unsigned width, unsigned shift, 
                                                                typename SolverContext::result_type isSigned, unsigned shiftBits);
    typename SolverContext::result_type constructMulByConstant(typename SolverContext::result_type expr, unsigned width, uint64_t x);
    typename SolverContext::result_type constructUDivByConstant(typename SolverContext::result_type expr_n, unsigned width, uint64_t d);
    typename SolverContext::result_type constructSDivByConstant(typename SolverContext::result_type expr_n, unsigned width, uint64_t d);
    
    unsigned getShiftBits(unsigned amount);
};

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::getArrayForUpdate(uint32_t arrayId, uint32_t updateNodeId) {
  if (updateNodeId == 0) {
    return(getInitialArray(arrayId));
  }
  else {
    assert(updateNodeId < updateNodeList.size() && "Out of bounds update node ID");
    serialization::UpdateNode::Reader un = updateNodeList[updateNodeId];
    typename SolverContext::result_type un_expr;
    
    auto it = updateNodeCache.find(updateNodeId); 
    
    if(it != updateNodeCache.end()){
//    if(false){
      un_expr = it->second;
    } else {
      un_expr = metaSMT::evaluate(solver,
          metaSMT::logic::Array::store(getArrayForUpdate(arrayId, un.getNextNodeId()),
              deserialize(un.getIndexExprId(), 0),
              deserialize(un.getValueExprId(), 0)));
      updateNodeCache[updateNodeId] = un_expr;
    }
    return(un_expr);
  }
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::getInitialArray(uint32_t arrayId)
{
  typename SolverContext::result_type array_expr;
  
  auto it = arrayCache.find(arrayId);
  if(it != arrayCache.end()){
    array_expr = it->second;
  } else {
    serialization::Array::Reader root = arrayList[arrayId];
    array_expr = metaSMT::evaluate(solver, buildArray(root.getRange(), root.getDomain()));
    
    if (root.isConstantIds()) {
      capnp::List<uint32_t>::Reader constants = root.getConstantIds();
      unsigned constantsSize = constants.size();
      assert((constantsSize == root.getSize()) && "Array size mismatch: Array size doesn't equal number of constant elements");
      for (unsigned i = 0, e = constantsSize; i != e; ++i) {
        typename SolverContext::result_type tmp =
            metaSMT::evaluate(solver, 
                metaSMT::logic::Array::store(array_expr,
                    aPIntToMetaSMTConstant(llvm::APIntLite(root.getDomain(), i)),
                    aPIntToMetaSMTConstant(constantToAPInt(exprList[constants[i]], 0))));
        array_expr = tmp;
      }
    }
    arrayCache[arrayId] = array_expr;
  }
  
  return(array_expr);
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::getInitialRead(uint32_t arrayId, uint32_t index) {
  typename SolverContext::result_type array_exp = getInitialArray(arrayId);
  typename SolverContext::result_type res = metaSMT::evaluate(
      solver,
      metaSMT::logic::Array::select(array_exp, metaSMT::logic::QF_BV::bvuint(index, arrayList[arrayId].getDomain())));    
  return(res);
}

template<typename SolverContext>
uint64_t MetaSMTDeserializer<SolverContext>::constantToZExtValue(serialization::Expr::Reader constantExpr){
  assert(constantExpr.isConstantExpr() && 
      "MetaSMTDeserializer::constantToZExtValue(): Called with a non-constant expression parameter");
  serialization::Expr::ConstantExpr::Reader constant = constantExpr.getConstantExpr();
  
  uint32_t width = constantExpr.getWidth();
  assert(width <= 64 && "Value is more than 64 bits wide and will be truncated.");
//  uint64_t val = *((const uint64_t*) constant.getValue().begin());
//  return val;
  
  if(constant.isWord()){
    return constant.getWord();
  } else {
    return constant.getWords()[0];
  }
}

template<typename SolverContext>
llvm::APIntLite MetaSMTDeserializer<SolverContext>::constantToAPInt(serialization::Expr::Reader constantExpr, int* width_out){
  assert(constantExpr.isConstantExpr() && 
      "MetaSMTDeserializer::constantToAPInt(): Called with a non-constant expression parameter");
  serialization::Expr::ConstantExpr::Reader constant = constantExpr.getConstantExpr();
  uint32_t width = constantExpr.getWidth();
  if(width_out)
    *width_out = width;
  
//  capnp::Data::Reader constantData = constant.getValue();
//  const void* address = constantData.begin();
//  
//  switch (width) {
//    case  1: return constantToAPInt(*((const uint8_t*) address), width);
//    case  8: return constantToAPInt(*((const uint8_t*) address), width);
//    case 16: return constantToAPInt(*((const uint16_t*) address), width);
//    case 32: return constantToAPInt(*((const uint32_t*) address), width);
//    case 64: return constantToAPInt(*((const uint64_t*) address), width);
//    default:
//      return llvm::APIntLite(width, (width+llvm::integerPartWidth-1) / llvm::integerPartWidth, (const uint64_t*)address);
//  }
  
  llvm::APIntLite val;
  if(constant.isWord()){
    val = constantToAPInt(constant.getWord(), width);
  } else {
    capnp::List<uint64_t>::Reader wordList = constant.getWords();
    unsigned wordCount = wordList.size(); 
    uint64_t words[wordCount];
    std::cerr << "Words: ";
    for(unsigned i = 0; i < wordCount; ++i){
      words[i] = (uint64_t)(wordList[i]);
      std::cerr << wordList[i] << "->" << words[i] << " ";
    }
    std::cerr << "\n";
    val = constantToAPInt(words, wordCount, width);
    const uint64_t* vals = val.getRawData();
    uint32_t numWords = val.getNumWords();
    std::cerr << "Words (failing): ";
    for(unsigned i = 0; i < numWords; ++i){
      std::cerr << (uint64_t)(vals[i]) << " ";
    }
    std::cerr << "\n";
  }
  return val;
}

template<typename SolverContext>
llvm::APIntLite MetaSMTDeserializer<SolverContext>::constantToAPInt(uint64_t value, uint32_t width){
  assert(value == (value&(((uint64_t) (int64_t) -1) >> (64 - width))) && "invalid constant");
  return llvm::APIntLite(width, value);
}

template<typename SolverContext>
llvm::APIntLite MetaSMTDeserializer<SolverContext>::constantToAPInt(uint64_t* values, uint32_t numWords, uint32_t width){
  std::cerr << "Words(" << width << "): ";
  for(unsigned i = 0; i < numWords; ++i){
    std::cerr << values[i] << " ";
  }
  std::cerr << "\n";
  return llvm::APIntLite(width, numWords, values);
}

template<typename SolverContext>
template<typename Arg>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::aPIntToMetaSMTConstant(Arg&& val){
  typename SolverContext::result_type res;
  
  unsigned width = val.getBitWidth();
  
//  std::cerr << "C: " << val.getZExtValue() << "\n";
  
  // Coerce to bool if necessary.
  if (width == 1) {
    res = (val.getBoolValue()) ? getTrue() : getFalse();
  }
  else if (width <= 32) {
    res = bvConst32(width, val.getZExtValue());
  }
  else if (width <= 64) {
    res = bvConst64(width, val.getZExtValue());
  }
  else {
    llvm::APIntLite tmp = val;
    unsigned tmpWidth = tmp.getBitWidth();
    res = bvConst64(64, (llvm::APIntLite(val.ashr(0)).zextOrTrunc(64)).getZExtValue());
    while (tmpWidth > 64) {
      tmp = (llvm::APIntLite(val.ashr(64)).zextOrTrunc(tmpWidth - 64));
      tmpWidth = tmp.getBitWidth();
      unsigned min_width = std::min(64U, tmpWidth);
      res = metaSMT::evaluate(solver,
          metaSMT::logic::QF_BV::concat(bvConst64(min_width, (tmp.zextOrTrunc(min_width)).getZExtValue()),
              res));
    }
  }
  
  return res;
}

template<typename SolverContext>
capnp::MessageBuilder&& MetaSMTDeserializer<SolverContext>::deserializeAndSolve(kj::ArrayPtr<const kj::ArrayPtr<const capnp::word>> bytes, capnp::MessageBuilder&& replyMsg){
  
//  int fd = open("tmpfile.capnp", O_RDWR | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH);
//  if(fd==-1)
//    std::cerr << "Error:" << errno << "\n";
//  capnp::writePackedMessageToFd(fd, bytes);
//  close(fd);
//  struct stat stat_buf;
//  int rc = stat("tmpfile.capnp", &stat_buf);
//  unsigned long querySize = stat_buf.st_size;
//  remove("tmpfile.capnp");
  
  unsigned long querySize = capnp::computeSerializedSizeInWords(bytes) * sizeof(capnp::word);
  ++cnt;
  avg = (querySize + ((cnt-1) * avg)) / cnt;
  if(querySize > max){
    max = querySize;
  }
  
  capnp::SegmentArrayMessageReader message(bytes);
  serialization::Query::Reader query = message.getRoot<serialization::Query>();
  
  serialization::Query::Data::Reader queryData = query.getData();
  exprList = queryData.getExprList();
  arrayList = queryData.getArrayList();
  updateNodeList = queryData.getUpdateNodeList();
  
  capnp::List<uint32_t>::Reader constraints = query.getConstraints();
  //std::cerr << "\nConstraints: " << constraints.size() << "\n";
  //std::cerr << "Expr: " << (int)(exprList[query.getExpression()].getKind()) << "\n";
  for(uint32_t exprId : constraints){
    metaSMT::assumption(solver, deserialize(exprId, 0));
  }
  
  metaSMT::assumption(solver, deserialize(query.getExpression(), 0));
  
  bool hasSolution = metaSMT::solve(solver);
  
  
  serialization::Reply::Builder reply = replyMsg.initRoot<serialization::Reply>();
  
  if (hasSolution){
    serialization::Reply::Sat::Builder sat = reply.initSat();
    
    if(query.isCounterExArrayIds()){
      capnp::List<uint32_t>::Reader counterExArrayIds = query.getCounterExArrayIds();
      unsigned counterExCount = counterExArrayIds.size();
      capnp::List<capnp::List<uint8_t>>::Builder counterExAssignments = sat.initAssignments(counterExCount);
      for (unsigned i = 0; i < counterExCount; ++i) {
        typename SolverContext::result_type array_exp = getInitialArray(counterExArrayIds[i]);
        
        unsigned arraySize = arrayList[counterExArrayIds[i]].getSize();
        uint32_t arrayDomain = arrayList[counterExArrayIds[i]].getDomain();
        capnp::List<uint8_t>::Builder counterExAssignment = counterExAssignments.init(i, arraySize);
        
        for (unsigned offset = 0; offset < arraySize; ++offset) {
          typename SolverContext::result_type elem_exp = metaSMT::evaluate(
              solver,
              metaSMT::logic::Array::select(array_exp, metaSMT::logic::QF_BV::bvuint(offset, arrayDomain)));
          unsigned char elem_value = metaSMT::read_value(solver, elem_exp);
          counterExAssignment.set(offset, (unsigned)(elem_value - '0'));
        }
      }
    } else {
      sat.setNoAssignment();
    }
  } else {
    reply.setUnsat();
  }
  
  exprCache.clear();
  arrayCache.clear();
  updateNodeCache.clear();
  
  return std::move(replyMsg);
}


/** if *width_out!=1 then result is a bitvector,
      otherwise it is a bool */
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::deserialize(uint32_t exprId, int *width_out) {
//  if (/*!useConstructCaching ||*/ (exprList[exprId].getKind() == serialization::Expr::Kind::CONSTANT)) {
//    return(deserializeActual(exprId, width_out));
//  } else {
    auto it = exprCache.find(exprId);
    if (it != exprCache.end()) {
      if (width_out) {
        *width_out = it->second.second;
      }
      return it->second.first;
    } else {
      int width = 0;
      if (!width_out) {
        width_out = &width;
      }
      typename SolverContext::result_type res = deserializeActual(exprId, width_out);
      exprCache[exprId] = std::make_pair(res, *width_out);
      return res;
    }
//  }
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::deserializeActual(uint32_t exprId, int *width_out)  {
  serialization::Expr::Reader e = exprList[exprId];

  int width = 0;
  if (!width_out) { 
    // assert(false);
    width_out = &width;
  }
  
  ++stats::queryConstructs;
  
  //     llvm::errs() << "Constructing expression ";
  //     ExprPPrinter::printSingleExpr(llvm::errs(), e);
  //     llvm::errs() << "\n";
  
  switch (e.getKind()) {
    
    case serialization::Expr::Kind::CONSTANT:
    {
//std::cerr << "D - CONSTANT" << "\n";
      assert(e.isConstantExpr() && 
          "Expression type mismatch: kind is set to CONSTANT, but ConstantExpr field has not been set");
      llvm::APIntLite val = constantToAPInt(e, width_out);
      unsigned width = *width_out;
//std::cerr << "D - CONSTANT middle " << val.getBitWidth() << "\n";
      
      typename SolverContext::result_type res = aPIntToMetaSMTConstant(val);
      //std::cerr << "CONSTANT end\n";
      return res;
    }
    
    case serialization::Expr::Kind::NOT_OPTIMIZED:
//std::cerr << "D - NOT_OPTIMIZED" << "\n";
    {
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to NOT_OPTIMIZED, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to NOT_OPTIMIZED, but its readExpr or extractExpr field is set");
      typename SolverContext::result_type res = deserialize((nonConst.getKidIds())[0], width_out); 
//std::cerr << "NOT_OPTIMIZED end" << "\n";
      return res;
    }
    
    case serialization::Expr::Kind::SELECT:
    {
//std::cerr << "D - SELECT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to SELECT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to SELECT, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      typename SolverContext::result_type res = metaSMT::evaluate(solver, 
          metaSMT::logic::Ite(deserialize(kids[0], 0), 
              deserialize(kids[1], width_out),
              deserialize(kids[2], width_out))); 
//std::cerr << "SELECT end" << "\n";
      return res;
    }
    
    case serialization::Expr::Kind::READ:
    {
//std::cerr << "D - READ" << "\n";
      assert(e.isNonConstantExpr() && 
          "Expression type mismatch: kind is set to READ, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isReadExpr() && 
          "Expression type mismatch: kind is set to READ, but its readExpr field is not set");
      serialization::UpdateList::Reader updates = nonConst.getReadExpr().getUpdateList();
      
      *width_out = e.getWidth();
      
      typename SolverContext::result_type res = metaSMT::evaluate(solver, 
          metaSMT::logic::Array::select(
              getArrayForUpdate(updates.getArray(), updates.getHeadNodeId()),
              deserialize((nonConst.getKidIds())[0], 0)));
//std::cerr << "READ end\n";
      return res;
    }
    
    case serialization::Expr::Kind::CONCAT:
    {
//std::cerr << "D - CONCAT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to CONCAT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to CONCAT, but its readExpr or extractExpr field is set");
      *width_out = e.getWidth();
      
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      unsigned numKids = kids.size();
      
      typename SolverContext::result_type res;
      if (numKids > 0) {
//        res = metaSMT::evaluate(solver, deserialize(kids[0], 0));
//        for (unsigned i = 1; i < numKids; ++i) {
//          res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(deserialize(kids[i], 0), res));
//        }
        res = metaSMT::evaluate(solver, deserialize(kids[numKids-1], 0));
        for (unsigned i = 2; i <= numKids; ++i) {
          res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(deserialize(kids[numKids - i], 0), res));
        }
      } else {
        //std::cerr << "WARNING: CONCAT expression with 0 child expressions\n";
      }
      //std::cerr << "CONCAT end\n";
      return res;
    }
    
    case serialization::Expr::Kind::EXTRACT:
    {
//std::cerr << "D - EXTRACT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to EXTRACT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isExtractExpr() && 
                "Expression type mismatch: kind is set to EXTRACT, but its extractExpr field is not set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      // ToDo spare evaluate?
      typename SolverContext::result_type child = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      
      uint32_t width = e.getWidth();
      *width_out = width;
      
      uint32_t offset = nonConst.getExtractExpr().getOffset();
      if (width == 1) {
        return bvBoolExtract(child, offset);
      }
      else {
        return metaSMT::evaluate(solver,
            metaSMT::logic::QF_BV::extract(offset + width - 1, offset, child));
      }
    }
    
    case serialization::Expr::Kind::Z_EXT:
    {
//std::cerr << "D - Z_EXT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to Z_EXT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to Z_EXT, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      int child_width = 0;
      typename SolverContext::result_type child = metaSMT::evaluate(solver, deserialize(kids[0], &child_width));
      
      uint32_t width = e.getWidth();
      *width_out = width;
      
      if (child_width == 1) {
        return metaSMT::evaluate(solver, 
            metaSMT::logic::Ite(child, bvOne(width), bvZero(width)));                          
      }
      else {
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::zero_extend(width - child_width, child));
      }
      
      // ToDo calculate how many zeros to add
      // Note: STP and metaSMT differ in the prototype arguments;
      // STP requires the width of the resulting bv;
      // whereas metaSMT (and Z3) require the width of the zero vector that is to be appended
      // res = metaSMT::evaluate(solver, zero_extend(ce_width, deserialize(ce->src)));
    }
    
    case serialization::Expr::Kind::S_EXT:
    {
//std::cerr << "D - S_EXT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to S_EXT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to S_EXT, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      int child_width = exprList[kids[0]].getWidth();
      //std::cerr << "S_EXT " << (int)(exprList[kids[0]].getKind()) << " " << exprList[kids[0]].getNonConstantExpr().getKidIds().size() << "\n";
      typename SolverContext::result_type child = metaSMT::evaluate(solver, deserialize(kids[0], 0));
      
      uint32_t width = e.getWidth();
      *width_out = width;
      
      if (child_width == 1) {
        return metaSMT::evaluate(solver, 
            metaSMT::logic::Ite(child, bvMinusOne(width), bvZero(width)));
      }
      else {
        // ToDo ce_width - child_width? It is only ce_width in STPBuilder
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::sign_extend(width - child_width, child));
      }
    }
    
    case serialization::Expr::Kind::ADD:
    {
//std::cerr << "D - ADD" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to ADD, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to ADD, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      typename SolverContext::result_type res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvadd(deserialize(kids[0], width_out), deserialize(kids[1], width_out)));
      assert(*width_out != 1 && "uncanonicalized add");
      return res;
    }  
    
    case serialization::Expr::Kind::SUB:
    {
//std::cerr << "D - SUB" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to SUB, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to SUB, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      typename SolverContext::result_type res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(deserialize(kids[0], width_out), deserialize(kids[1], width_out))); 
      assert(*width_out != 1 && "uncanonicalized sub");
      return res;   
    }  
    
    case serialization::Expr::Kind::MUL:
    {
//std::cerr << "D - MUL" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to MUL, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to MUL, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      assert(*width_out != 1 && "uncanonicalized mul");
      
      serialization::Expr::Reader left = exprList[kids[0]];
      if ((left.isConstantExpr()) && (left.getWidth() <= 64)) {   
        return constructMulByConstant(right_expr, *width_out, constantToZExtValue(left));  
      }
      else {
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvmul(deserialize(kids[0], width_out), right_expr));      
      }
    }
    
    case serialization::Expr::Kind::U_DIV:
    {
//std::cerr << "D - U_DIV" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to U_DIV, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to U_DIV, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = deserialize(kids[0], width_out);
      assert(*width_out != 1 && "uncanonicalized udiv");
      
      serialization::Expr::Reader right = exprList[kids[1]];
      if ((right.getKind() == serialization::Expr::Kind::CONSTANT) && (right.getWidth() <= 64)) {   
        uint64_t divisor = constantToZExtValue(right);
        if (bits64::isPowerOfTwo(divisor)) {
          return bvRightShift(left_expr, *width_out, bits64::indexOfSingleBit(divisor), getShiftBits(*width_out));
        }
        else if (optimizeDivides) {
          if (*width_out == 32) { //only works for 32-bit division
            return constructUDivByConstant(left_expr, *width_out, (unsigned) divisor);
          }
        }
      }
      
      return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvudiv(left_expr, deserialize(kids[1], width_out))); 
    }
    
    case serialization::Expr::Kind::S_DIV:
    {
//std::cerr << "D - S_DIV" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to S_DIV, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to S_DIV, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = deserialize(kids[0], width_out);
      assert(*width_out != 1 && "uncanonicalized sdiv");
      
      serialization::Expr::Reader right = exprList[kids[1]];
      if ((right.getKind() == serialization::Expr::Kind::CONSTANT) && optimizeDivides && (*width_out == 32)) {   
        return constructSDivByConstant(left_expr, *width_out, constantToZExtValue(right));
      }
      else {
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsdiv(left_expr, deserialize(kids[1], width_out))); 
      }
    }
    
    case serialization::Expr::Kind::U_REM:
    {
//std::cerr << "D - U_REM" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to U_REM, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to U_REM, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = deserialize(kids[0], width_out);
      assert(*width_out != 1 && "uncanonicalized urem");
      
      bool construct_both = true;
      typename SolverContext::result_type res;
      serialization::Expr::Reader right = exprList[kids[1]];
      if ((right.getKind() == serialization::Expr::Kind::CONSTANT) && (right.getWidth() <= 64)) {
        uint64_t divisor = constantToZExtValue(right);
        
        if (bits64::isPowerOfTwo(divisor)) {
          
          unsigned bits = bits64::indexOfSingleBit(divisor);    
          // special case for modding by 1 or else we bvExtract -1:0
          if (bits == 0) {
            res = bvZero(*width_out);
            construct_both = false;
          }
          else {
            res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(bvZero(*width_out - bits), 
                bvExtract(left_expr, bits - 1, 0)));
            construct_both = false;
          }
        }
        
        // Use fast division to compute modulo without explicit division for constant divisor.
        
        if (optimizeDivides && *width_out == 32) { //only works for 32-bit division
          typename SolverContext::result_type quotient = constructUDivByConstant(left_expr, *width_out, (unsigned) divisor);
          typename SolverContext::result_type quot_times_divisor = constructMulByConstant(quotient, *width_out, divisor);
          res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(left_expr, quot_times_divisor));                    
          construct_both = false;
        }
      }
      
      if (construct_both) {
        res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvurem(left_expr, deserialize(kids[1], width_out)));       
      }
      
      return res;  
    }
    
    case serialization::Expr::Kind::S_REM:
    {
//std::cerr << "D - S_REM" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to S_REM, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to S_REM, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      assert(*width_out != 1 && "uncanonicalized srem");
      
      return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsrem(left_expr, right_expr));
    }
    
    case serialization::Expr::Kind::NOT:
    {
//std::cerr << "D - NOT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to NOT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to NOT, but its readExpr or extractExpr field is set");
      typename SolverContext::result_type child = metaSMT::evaluate(solver, deserialize(nonConst.getKidIds()[0], width_out));
      if (*width_out == 1) {
        return metaSMT::evaluate(solver, metaSMT::logic::Not(child));
      }
      else {                
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvnot(child));
      }    
    }
    
    case serialization::Expr::Kind::AND:
    {
//std::cerr << "D - AND" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to AND, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to AND, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      
      if (*width_out == 1) {
        return metaSMT::evaluate(solver, metaSMT::logic::And(left_expr, right_expr));
      }
      else {
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvand(left_expr, right_expr));
      }
    }
    
    case serialization::Expr::Kind::OR:
    {
//std::cerr << "D - OR" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to OR, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to OR, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      
      if (*width_out == 1) {
        return metaSMT::evaluate(solver, metaSMT::logic::Or(left_expr, right_expr));
      }
      else {
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvor(left_expr, right_expr));
      }
    }
    
    case serialization::Expr::Kind::XOR:
    {
//std::cerr << "D - XOR" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to XOR, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to XOR, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      
      if (*width_out == 1) {
        return metaSMT::evaluate(solver, metaSMT::logic::Xor(left_expr, right_expr));
      }
      else {
        return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvxor(left_expr, right_expr));
      }
    }
    
    case serialization::Expr::Kind::SHL:
    {
//std::cerr << "D - SHL" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to SHL, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to SHL, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      assert(*width_out != 1 && "uncanonicalized shl");
      
      serialization::Expr::Reader right = exprList[kids[1]];
      if (right.getKind() == serialization::Expr::Kind::CONSTANT) {
        return  bvLeftShift(left_expr, *width_out, (unsigned)(constantToAPInt(right, 0).getLimitedValue()), getShiftBits(*width_out));
      }
      else {
        int shiftWidth = 0;
        typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], &shiftWidth));
        return mimic_stp ? bvVarLeftShift(left_expr, right_expr, *width_out) : metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvshl(left_expr, right_expr));       
      }    
    }
    
    case serialization::Expr::Kind::L_SHR:
    {
//std::cerr << "D - L_SHR" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to L_SHR, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to L_SHR, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));     
      assert(*width_out != 1 && "uncanonicalized lshr");
      
      serialization::Expr::Reader right = exprList[kids[1]];
      if (right.getKind() == serialization::Expr::Kind::CONSTANT) {
        return  bvRightShift(left_expr, *width_out, (unsigned)(constantToAPInt(right, 0).getLimitedValue()), getShiftBits(*width_out));
      }
      else {
        int shiftWidth = 0;
        typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], &shiftWidth));
        return mimic_stp ? bvVarRightShift(left_expr, right_expr, *width_out) : metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvshr(left_expr, right_expr));
      }
    }
    
    case serialization::Expr::Kind::A_SHR:
    {
//std::cerr << "D - A_SHR" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to A_SHR, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to A_SHR, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));     
      assert(*width_out != 1 && "uncanonicalized ashr");
      
      serialization::Expr::Reader right = exprList[kids[1]];
      if (right.getKind() == serialization::Expr::Kind::CONSTANT) {
        unsigned shift = (unsigned)(constantToAPInt(right, 0).getLimitedValue());
        typename SolverContext::result_type signedBool = bvBoolExtract(left_expr, *width_out - 1);
        return constructAShrByConstant(left_expr, *width_out, shift, signedBool, getShiftBits(*width_out));       
      }
      else {
        int shiftWidth = 0;
        typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], &shiftWidth));
        return mimic_stp ? bvVarArithRightShift(left_expr, right_expr, *width_out) : metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvashr(left_expr, right_expr)); 
      }    
    }
    
    case serialization::Expr::Kind::EQ:
    {
//std::cerr << "D - EQ" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to EQ, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to EQ, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      
      typename SolverContext::result_type res;
      
      if (*width_out==1) {
        serialization::Expr::Reader left = exprList[kids[0]];
        if (left.getKind() == serialization::Expr::Kind::CONSTANT) {
          if (constantToAPInt(left,0).getBoolValue()) {
            res = right_expr;  
          }
          else {
            res = metaSMT::evaluate(solver, metaSMT::logic::Not(right_expr));
          }
        }
        else {
          res = metaSMT::evaluate(solver, metaSMT::logic::equal(left_expr, right_expr));
        }
      } // end of *width_out == 1
      else {
        *width_out = 1;
        res = metaSMT::evaluate(solver, metaSMT::logic::equal(left_expr, right_expr));
      }
      
      //std::cerr << "EQ end\n";
      
      return res;
    }
    
    case serialization::Expr::Kind::ULT:
    {
//std::cerr << "D - ULT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to ULT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to ULT, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));     
      
      assert(*width_out != 1 && "uncanonicalized ult");
      *width_out = 1;    
      
      return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvult(left_expr, right_expr));
    }
    
    case serialization::Expr::Kind::ULE:
    {
//std::cerr << "D - ULE" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to ULE, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to ULE, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out)); 
      
      assert(*width_out != 1 && "uncanonicalized ule");
      *width_out = 1;    
      
      return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvule(left_expr, right_expr));
    }
    
    case serialization::Expr::Kind::SLT:
    {
//std::cerr << "D - SLT" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to SLT, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to SLT, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out)); 
      
      assert(*width_out != 1 && "uncanonicalized slt");
      *width_out = 1;
      
      return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvslt(left_expr, right_expr));
    }
    
    case serialization::Expr::Kind::SLE:
    {
//std::cerr << "D - SLE" << "\n";
      assert(e.isNonConstantExpr() && 
                "Expression type mismatch: kind is set to SLE, but its fields indicate a constant expression");
      
      serialization::Expr::NonConstantExpr::Reader nonConst = e.getNonConstantExpr();
      assert(nonConst.isOtherNonConst() && 
          "Expression type mismatch: kind is set to SLE, but its readExpr or extractExpr field is set");
      capnp::List<uint32_t>::Reader kids = nonConst.getKidIds();
      
      typename SolverContext::result_type left_expr = metaSMT::evaluate(solver, deserialize(kids[0], width_out));
      typename SolverContext::result_type right_expr = metaSMT::evaluate(solver, deserialize(kids[1], width_out));
      
      assert(*width_out != 1 && "uncanonicalized sle");
      *width_out = 1;    
      
      return metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsle(left_expr, right_expr));
    }
    
    // unused due to canonicalization
#if 0
    case serialization::Expr::Kind::NE:
    case serialization::Expr::Kind::UGT:
    case serialization::Expr::Kind::UGE:
    case serialization::Expr::Kind::SGT:
    case serialization::Expr::Kind::SGE:
#endif  
      
    default:
      assert(false);
      typename SolverContext::result_type res;
      return res;      
  };
}

template<typename SolverContext>
MetaSMTArray MetaSMTDeserializer<SolverContext>::buildArray(unsigned elem_width, unsigned index_width) {
  return(metaSMT::logic::Array::new_array(elem_width, index_width));
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::getTrue() {
  return(metaSMT::evaluate(solver, metaSMT::logic::True));        
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::getFalse() {        
  return(metaSMT::evaluate(solver, metaSMT::logic::False));        
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvOne(unsigned width) {
  return bvZExtConst(width, 1);
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvZero(unsigned width) {
  return bvZExtConst(width, 0);
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvMinusOne(unsigned width) {
  return bvSExtConst(width, (int64_t) -1);
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvConst32(unsigned width, uint32_t value) {
  return(metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvuint(value, width)));
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvConst64(unsigned width, uint64_t value) {
  return(metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvuint(value, width)));
}

template<typename SolverContext>  
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvZExtConst(unsigned width, uint64_t value) {
  
  typename SolverContext::result_type res;
  
  if (width <= 64) {
    res = bvConst64(width, value);
  }
  else {
    typename SolverContext::result_type expr = bvConst64(64, value);
    typename SolverContext::result_type zero = bvConst64(64, 0);
    
    for (width -= 64; width > 64; width -= 64) {
      expr = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(zero, expr));  
    }
    res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(bvConst64(width, 0), expr));  
  }
  
  return(res); 
}

template<typename SolverContext>  
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvSExtConst(unsigned width, uint64_t value) {
  
  typename SolverContext::result_type res;
  
  if (width <= 64) {
    res = bvConst64(width, value); 
  }
  else {            
    // ToDo Reconsider -- note differences in STP and metaSMT for sign_extend arguments
    res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::sign_extend(width - 64, bvConst64(64, value)));       
  }
  return(res); 
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvBoolExtract(typename SolverContext::result_type expr, int bit) {
  return(metaSMT::evaluate(solver,
      metaSMT::logic::equal(metaSMT::logic::QF_BV::extract(bit, bit, expr),
          bvOne(1))));
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvExtract(typename SolverContext::result_type expr, unsigned top, unsigned bottom) {    
  return(metaSMT::evaluate(solver, metaSMT::logic::QF_BV::extract(top, bottom, expr)));
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::eqExpr(typename SolverContext::result_type a, typename SolverContext::result_type b) {    
  return(metaSMT::evaluate(solver, metaSMT::logic::equal(a, b)));
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::constructAShrByConstant(typename SolverContext::result_type expr, unsigned width, unsigned amount,
    typename SolverContext::result_type isSigned, unsigned shiftBits) {
  unsigned shift = amount & ((1 << shiftBits) - 1);
  typename SolverContext::result_type res;
  
  if (shift == 0) {
    res = expr;
  }
  else if (shift >= width) {
    res = metaSMT::evaluate(solver, metaSMT::logic::Ite(isSigned, bvMinusOne(width), bvZero(width)));
  }
  else {
    res = metaSMT::evaluate(solver, metaSMT::logic::Ite(isSigned,
        metaSMT::logic::QF_BV::concat(bvMinusOne(shift), bvExtract(expr, width - 1, shift)),
        bvRightShift(expr, width, shift, shiftBits)));
  }
  
  return(res);
}

// width is the width of expr; x -- number of bits to shift with
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::constructMulByConstant(typename SolverContext::result_type expr, unsigned width, uint64_t x) {
  
  unsigned shiftBits = getShiftBits(width);
  uint64_t add, sub;
  typename SolverContext::result_type res;
  bool first = true;
  
  // expr*x == expr*(add-sub) == expr*add - expr*sub
  ComputeMultConstants64(x, add, sub);
  
  // legal, these would overflow completely
  add = bits64::truncateToNBits(add, width);
  sub = bits64::truncateToNBits(sub, width);
  
  for (int j = 63; j >= 0; j--) {
    uint64_t bit = 1LL << j;
    
    if ((add & bit) || (sub & bit)) {
      assert(!((add & bit) && (sub & bit)) && "invalid mult constants");
      
      typename SolverContext::result_type op = bvLeftShift(expr, width, j, shiftBits);
      
      if (add & bit) {
        if (!first) {
          res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvadd(res, op));
        } else {
          res = op;
          first = false;
        }
      } else {
        if (!first) {
          res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(res, op));                    
        } else {
          // To reconsider: vc_bvUMinusExpr in STP
          res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(bvZero(width), op));
          first = false;
        }
      }
    }
  }
  
  if (first) { 
    res = bvZero(width);
  }
  
  return(res);
}


/* 
 * Compute the 32-bit unsigned integer division of n by a divisor d based on 
 * the constants derived from the constant divisor d.
 *
 * Returns n/d without doing explicit division.  The cost is 2 adds, 3 shifts, 
 * and a (64-bit) multiply.
 *
 * @param expr_n numerator (dividend) n as an expression
 * @param width  number of bits used to represent the value
 * @param d      the divisor
 *
 * @return n/d without doing explicit division
 */
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::constructUDivByConstant(typename SolverContext::result_type expr_n, unsigned width, uint64_t d) {
  
  assert(width == 32 && "can only compute udiv constants for 32-bit division");
  
  // Compute the constants needed to compute n/d for constant d without division by d.
  uint32_t mprime, sh1, sh2;
  ComputeUDivConstants32(d, mprime, sh1, sh2);
  typename SolverContext::result_type expr_sh1 = bvConst32(32, sh1);
  typename SolverContext::result_type expr_sh2 = bvConst32(32, sh2);
  
  // t1  = MULUH(mprime, n) = ( (uint64_t)mprime * (uint64_t)n ) >> 32
  typename SolverContext::result_type expr_n_64 = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(bvZero(32), expr_n)); //extend to 64 bits
  typename SolverContext::result_type t1_64bits = constructMulByConstant(expr_n_64, 64, (uint64_t)mprime);
  typename SolverContext::result_type t1        = bvExtract(t1_64bits, 63, 32); //upper 32 bits
  
  // n/d = (((n - t1) >> sh1) + t1) >> sh2;
  typename SolverContext::result_type n_minus_t1 = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(expr_n, t1));   
  typename SolverContext::result_type shift_sh1  = bvVarRightShift(n_minus_t1, expr_sh1, 32);
  typename SolverContext::result_type plus_t1    = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvadd(shift_sh1, t1));    
  typename SolverContext::result_type res        = bvVarRightShift(plus_t1, expr_sh2, 32);
  
  return(res);
}

/* 
 * Compute the 32-bitnsigned integer division of n by a divisor d based on 
 * the constants derived from the constant divisor d.
 *
 * Returns n/d without doing explicit division.  The cost is 3 adds, 3 shifts, 
 * a (64-bit) multiply, and an XOR.
 *
 * @param n      numerator (dividend) as an expression
 * @param width  number of bits used to represent the value
 * @param d      the divisor
 *
 * @return n/d without doing explicit division
 */
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::constructSDivByConstant(typename SolverContext::result_type expr_n, unsigned width, uint64_t d) {
  
  assert(width == 32 && "can only compute udiv constants for 32-bit division");
  
  // Compute the constants needed to compute n/d for constant d w/o division by d.
  int32_t mprime, dsign, shpost;
  ComputeSDivConstants32(d, mprime, dsign, shpost);
  typename SolverContext::result_type expr_dsign  = bvConst32(32, dsign);
  typename SolverContext::result_type expr_shpost = bvConst32(32, shpost);
  
  // q0 = n + MULSH( mprime, n ) = n + (( (int64_t)mprime * (int64_t)n ) >> 32)
  int64_t mprime_64     = (int64_t)mprime;
  
  // ToDo Reconsider -- note differences in STP and metaSMT for sign_extend arguments
  typename SolverContext::result_type expr_n_64    = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::sign_extend(64 - width, expr_n));    
  typename SolverContext::result_type mult_64      = constructMulByConstant(expr_n_64, 64, mprime_64);
  typename SolverContext::result_type mulsh        = bvExtract(mult_64, 63, 32); //upper 32-bits    
  typename SolverContext::result_type n_plus_mulsh = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvadd(expr_n, mulsh));
  
  // Improved variable arithmetic right shift: sign extend, shift, extract.
  typename SolverContext::result_type extend_npm   = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::sign_extend(64 - width, n_plus_mulsh));    
  typename SolverContext::result_type shift_npm    = bvVarRightShift(extend_npm, expr_shpost, 64);
  typename SolverContext::result_type shift_shpost = bvExtract(shift_npm, 31, 0); //lower 32-bits
  
  /////////////
  
  // XSIGN(n) is -1 if n is negative, positive one otherwise
  typename SolverContext::result_type is_signed    = bvBoolExtract(expr_n, 31);
  typename SolverContext::result_type neg_one      = bvMinusOne(32);
  typename SolverContext::result_type xsign_of_n   = metaSMT::evaluate(solver, metaSMT::logic::Ite(is_signed, neg_one, bvZero(32)));    
  
  // q0 = (n_plus_mulsh >> shpost) - XSIGN(n)
  typename SolverContext::result_type q0           = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(shift_shpost, xsign_of_n));    
  
  // n/d = (q0 ^ dsign) - dsign
  typename SolverContext::result_type q0_xor_dsign = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvxor(q0, expr_dsign));    
  typename SolverContext::result_type res          = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::bvsub(q0_xor_dsign, expr_dsign));    
  
  return(res);
}

template<typename SolverContext>
unsigned MetaSMTDeserializer<SolverContext>::getShiftBits(unsigned amount) {
  unsigned bits = 1;
  amount--;
  while (amount >>= 1) {
    bits++;
  }
  return(bits);
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvLeftShift(typename SolverContext::result_type expr, unsigned width, unsigned amount, unsigned shiftBits) {
  
  typename SolverContext::result_type res;    
  unsigned shift = amount & ((1 << shiftBits) - 1);
  
  if (shift == 0) {
    res = expr;
  }
  else if (shift >= width) {
    res = bvZero(width);
  }
  else {
    // stp shift does "expr @ [0 x s]" which we then have to extract,
    // rolling our own gives slightly smaller exprs
    res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(metaSMT::logic::QF_BV::extract(width - shift - 1, 0, expr),
        bvZero(shift)));
  }
  
  return(res);
}

template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvRightShift(typename SolverContext::result_type expr, unsigned width, unsigned amount, unsigned shiftBits) {
  
  typename SolverContext::result_type res;    
  unsigned shift = amount & ((1 << shiftBits) - 1);
  
  if (shift == 0) {
    res = expr;
  } 
  else if (shift >= width) {
    res = bvZero(width);
  }
  else {
    res = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::concat(bvZero(shift),
        metaSMT::logic::QF_BV::extract(width - 1, shift, expr)));        
  }
  
  return(res);
}

// left shift by a variable amount on an expression of the specified width
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvVarLeftShift(typename SolverContext::result_type expr, typename SolverContext::result_type amount, unsigned width) {
  
  typename SolverContext::result_type res =  bvZero(width);
  
  int shiftBits = getShiftBits(width);
  
  //get the shift amount (looking only at the bits appropriate for the given width)
  typename SolverContext::result_type shift = metaSMT::evaluate(solver, metaSMT::logic::QF_BV::extract(shiftBits - 1, 0, amount));    
  
  //construct a big if-then-elif-elif-... with one case per possible shift amount
  for(int i = width - 1; i >= 0; i--) {
    res = metaSMT::evaluate(solver, metaSMT::logic::Ite(eqExpr(shift, bvConst32(shiftBits, i)),
        bvLeftShift(expr, width, i, shiftBits),
        res));
  }
  
  // If overshifting, shift to zero    
  res = metaSMT::evaluate(solver, metaSMT::logic::Ite(metaSMT::logic::QF_BV::bvult(shift, bvConst32(shiftBits, width)),
      res,
      bvZero(width)));                                                
  
  return(res);
}

// logical right shift by a variable amount on an expression of the specified width
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvVarRightShift(typename SolverContext::result_type expr, typename SolverContext::result_type amount, unsigned width) {
  
  typename SolverContext::result_type res = bvZero(width);
  
  int shiftBits = getShiftBits(width);
  
  //get the shift amount (looking only at the bits appropriate for the given width)
  typename SolverContext::result_type shift = bvExtract(amount, shiftBits - 1, 0);
  
  //construct a big if-then-elif-elif-... with one case per possible shift amount
  for (int i = width - 1; i >= 0; i--) {
    res = metaSMT::evaluate(solver, metaSMT::logic::Ite(eqExpr(shift, bvConst32(shiftBits, i)),
        bvRightShift(expr, width, i, shiftBits),
        res));
    // ToDo Reconsider widht to provide to bvRightShift
  }
  
  // If overshifting, shift to zero
  res = metaSMT::evaluate(solver, metaSMT::logic::Ite(metaSMT::logic::QF_BV::bvult(shift, bvConst32(shiftBits, width)),
      res,
      bvZero(width)));                                                
  
  return(res);
}

// arithmetic right shift by a variable amount on an expression of the specified width
template<typename SolverContext>
typename SolverContext::result_type MetaSMTDeserializer<SolverContext>::bvVarArithRightShift(typename SolverContext::result_type expr, typename SolverContext::result_type amount, unsigned width) {
  
  int shiftBits = getShiftBits(width);
  
  //get the shift amount (looking only at the bits appropriate for the given width)
  typename SolverContext::result_type shift = bvExtract(amount, shiftBits - 1, 0);
  
  //get the sign bit to fill with
  typename SolverContext::result_type signedBool = bvBoolExtract(expr, width - 1);
  
  //start with the result if shifting by width-1
  typename SolverContext::result_type res =  constructAShrByConstant(expr, width, width - 1, signedBool, shiftBits);
  
  // construct a big if-then-elif-elif-... with one case per possible shift amount
  // XXX more efficient to move the ite on the sign outside all exprs?
  // XXX more efficient to sign extend, right shift, then extract lower bits?
  for (int i = width - 2; i >= 0; i--) {
    res = metaSMT::evaluate(solver, metaSMT::logic::Ite(eqExpr(shift, bvConst32(shiftBits,i)),
        constructAShrByConstant(expr, width, i, signedBool, shiftBits),
        res));
  }
  
  // If overshifting, shift to zero
  res = metaSMT::evaluate(solver, metaSMT::logic::Ite(metaSMT::logic::QF_BV::bvult(shift, bvConst32(shiftBits, width)),
      res,
      bvZero(width)));      
  
  return(res);
}

}  /* end of namespace klee */

#endif /* METASMTDESERIALIZER_H_ */
