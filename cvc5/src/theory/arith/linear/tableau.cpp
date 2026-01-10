/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "base/output.h"
#include "theory/arith/linear/tableau.h"

using namespace std;
namespace cvc5::internal {
namespace theory {
namespace arith::linear {


void Tableau::pivot(ArithVar oldBasic, ArithVar newBasic, CoefficientChangeCallback& cb){
  Assert(isBasic(oldBasic));
  Assert(!isBasic(newBasic));
  Assert(d_mergeBuffer.empty());

  Trace("tableau") << "Tableau::pivot(" <<  oldBasic <<", " << newBasic <<")"  << endl;

  RowIndex ridx = basicToRowIndex(oldBasic);

  rowPivot(oldBasic, newBasic, cb);
  Assert(ridx == basicToRowIndex(newBasic));

  loadRowIntoBuffer(ridx);

  ColIterator colIter = colIterator(newBasic);
  while(!colIter.atEnd()){
    EntryID id = colIter.getID();
    Entry& entry = d_entries.get(id);

    ++colIter; //needs to be incremented before the variable is removed
    if(entry.getRowIndex() == ridx){ continue; }

    RowIndex to = entry.getRowIndex();
    Rational coeff = entry.getCoefficient();
    if(cb.canUseRow(to)){
      rowPlusBufferTimesConstant(to, coeff, cb);
    }else{
      rowPlusBufferTimesConstant(to, coeff);
    }
  }
  clearBuffer();

  //Clear the column for used for this variable

  Assert(d_mergeBuffer.empty());
  Assert(!isBasic(oldBasic));
  Assert(isBasic(newBasic));
  Assert(getColLength(newBasic) == 1);
}

/**
 * Changes basic to newbasic (a variable on the row).
 */
void Tableau::rowPivot(ArithVar basicOld, ArithVar basicNew, CoefficientChangeCallback& cb){
  Assert(isBasic(basicOld));
  Assert(!isBasic(basicNew));

  RowIndex rid = basicToRowIndex(basicOld);

  EntryID newBasicID = findOnRow(rid, basicNew);

  Assert(newBasicID != ENTRYID_SENTINEL);

  Tableau::Entry& newBasicEntry = d_entries.get(newBasicID);
  const Rational& a_rs = newBasicEntry.getCoefficient();
  int a_rs_sgn = a_rs.sgn();
  Rational negInverseA_rs = -(a_rs.inverse());

  for(RowIterator i = basicRowIterator(basicOld); !i.atEnd(); ++i){
    EntryID id = i.getID();
    Tableau::Entry& entry = d_entries.get(id);

    entry.getCoefficient() *=  negInverseA_rs;
  }

  d_basic2RowIndex.remove(basicOld);
  d_basic2RowIndex.set(basicNew, rid);
  d_rowIndex2basic.set(rid, basicNew);

  cb.multiplyRow(rid, -a_rs_sgn);
}

void Tableau::addRow(ArithVar basic,
                     const std::vector<Rational>& coefficients,
                     const std::vector<ArithVar>& variables)
{
  Assert(basic < getNumColumns());
  Assert(debugIsASet(variables));
  Assert(coefficients.size() == variables.size());
  Assert(!isBasic(basic));
  Assert(!isQuasiBasic(basic));

  RowIndex newRow = Matrix<Rational>::addRow(coefficients, variables);
  addEntry(newRow, basic, Rational(-1));

  Assert(!d_basic2RowIndex.isKey(basic));
  Assert(!d_rowIndex2basic.isKey(newRow));
  Assert(!d_quasiBasic2RowIndex.isKey(basic));

  d_basic2RowIndex.set(basic, newRow);
  d_rowIndex2basic.set(newRow, basic);


  if(TraceIsOn("matrix")){ printMatrix(); }

  NoEffectCCCB noeffect;
  NoEffectCCCB* nep = &noeffect;
  CoefficientChangeCallback* cccb = static_cast<CoefficientChangeCallback*>(nep);

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();
  for(; varsIter != varsEnd; ++coeffIter, ++varsIter){
    ArithVar var = *varsIter;

    if(isBasic(var) || isQuasiBasic(var)){
      Rational coeff = *coeffIter;

      RowIndex ri = isBasic(var) ? basicToRowIndex(var) : quasiBasicToRowIndex(var);

      loadRowIntoBuffer(ri);
      rowPlusBufferTimesConstant(newRow, coeff, *cccb);
      clearBuffer();
    }
  }

  if(TraceIsOn("matrix")) { printMatrix(); }

  Assert(debugNoZeroCoefficients(newRow));
  Assert(debugMatchingCountsForRow(newRow));
  Assert(getColLength(basic) == 1);
}

void Tableau::removeBasicRow(ArithVar basic){
  Assert(isBasic(basic) || isQuasiBasic(basic));
  
  RowIndex rid;
  if(isBasic(basic)){
    rid = basicToRowIndex(basic);
    d_basic2RowIndex.remove(basic);
    d_rowIndex2basic.remove(rid);
  }else{
    rid = quasiBasicToRowIndex(basic);
    d_quasiBasic2RowIndex.remove(basic);
  }

  removeRow(rid);
}

void Tableau::substitutePlusTimesConstant(ArithVar to, ArithVar from, const Rational& mult,  CoefficientChangeCallback& cb){
  if(!mult.isZero()){
    RowIndex to_idx = basicToRowIndex(to);
    addEntry(to_idx, from, mult); // Add an entry to be cancelled out
    RowIndex from_idx = basicToRowIndex(from);

    cb.update(to_idx, from, 0, mult.sgn());

    loadRowIntoBuffer(from_idx);
    rowPlusBufferTimesConstant(to_idx, mult, cb);
    clearBuffer();
  }
}

uint32_t Tableau::rowComplexity(ArithVar basic) const{
  uint32_t complexity = 0;
  for(RowIterator i = basicRowIterator(basic); !i.atEnd(); ++i){
    const Entry& e = *i;
    complexity += e.getCoefficient().complexity();
  }
  return complexity;
}

double Tableau::avgRowComplexity() const{
  double sum = 0;
  uint32_t rows = 0;
  for(BasicIterator i = beginBasic(), i_end = endBasic(); i != i_end; ++i){
    sum += rowComplexity(*i);
    rows++;
  }
  return (rows == 0) ? 0 : (sum/rows);
}

void Tableau::printBasicRow(ArithVar basic, std::ostream& out){
  if(isBasic(basic)){
    printRow(basicToRowIndex(basic), out);
  }else if(isQuasiBasic(basic)){
    printRow(quasiBasicToRowIndex(basic), out);
  }
}

void Tableau::quasiToBasic(ArithVar v, CoefficientChangeCallback& cb){
  Assert(isQuasiBasic(v));
  
  RowIndex rid = quasiBasicToRowIndex(v);
  
  // The row already exists in the Matrix, we just need to:
  // 1. Add entries from this row to the columns of non-basic variables
  // 2. Move from quasi-basic tracking to basic tracking
  
  // Add the row entries to columns (they should already be there from Matrix)
  // Actually, in cvc5's Matrix implementation, entries are automatically
  // added to both row and column. So we just need to update tracking.
  
  // Move from quasi-basic to basic tracking
  d_quasiBasic2RowIndex.remove(v);
  d_basic2RowIndex.set(v, rid);
  d_rowIndex2basic.set(rid, v);
  
  Assert(isBasic(v));
}

void Tableau::basicToQuasi(ArithVar v){
  Assert(isBasic(v));
  
  RowIndex rid = basicToRowIndex(v);
  
  // Move from basic to quasi-basic tracking
  // The row remains in the Matrix, but we remove it from basic tracking
  d_basic2RowIndex.remove(v);
  d_rowIndex2basic.remove(rid);
  d_quasiBasic2RowIndex.set(v, rid);
  
  Assert(isQuasiBasic(v));
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
