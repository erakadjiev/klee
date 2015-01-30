//===-- SMTLIBOutputLexer.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef SMTLIBOUTPUTLEXER_H_
#define SMTLIBOUTPUTLEXER_H_

#include <istream>
#include <string>

namespace klee
{

	/// This is a helper class for SMTLIBSolverImpl
	///
	//  This class will lex the input (e.g. ASCII text file) that is assumed to be the
	/// the output from a SMTLIBv2 conforming solver.
	///
	/// It should be noted this lexer is very basic and only supports a sub-set of the possible
	/// output from a conforming SMTLIBv2 solver.
	class SMTLIBOutputLexer
	{
		public:

			///This is a restricted set of the possible output tokens from a SMTLIBv2 solver
			enum Token
			{
				SAT_TOKEN, ///< "sat"
				UNSAT_TOKEN, ///< "unsat"
				UNKNOWN_TOKEN, //< "unknown"
				LBRACKET_TOKEN, ///< "("
				RBRACKET_TOKEN, ///< ")"
				SELECT_TOKEN, ///< "select"
				ARRAY_IDENTIFIER_TOKEN, //< Array identitfier matching [A-Za-z_0-9]+
				NUMERAL_BASE10_TOKEN, ///< "(_ bv1 8)"
				NUMERAL_BASE16_TOKEN, ///< "#x01"
				NUMERAL_BASE2_TOKEN, ///< "#b00000001"
				END_OF_FILE_TOKEN, ///< End of file.
				UNRECOGNISED_TOKEN /// < Unrecognised token.
			};

			SMTLIBOutputLexer();

			///Retrieve the next token.
			/// \param t . The found token will be placed here
			/// \return true is success.
			bool getNextToken(Token& t);

			///Set the input stream to use
			/// The old input stream will not be closed.
			void setInput(std::istream& i);

			///Get the current input stream in use
			std::istream& getInput();

			///Get the string that matched the last token found
			/// \sa getNextToken()
			const std::string& getLastTokenContents();

			///Determines the numeric value of the last numeral that was found using getNextToken()
			/// \param value is where the last found numeric value was placed
			/// \return true if there is a numeric value available and the numeric value will fit inside a long int.
			bool getLastNumericValue(unsigned long int& value);

		private:
			std::istream* input;
			std::string lastTokenContents;
			std::string lastNumericTokenValue;//Contains the numeral without type prefix

			char lastChar;

			//Walks through the input ignore whitespace and new lines.
			//After execution lastChar will contain the next non "white-space" character.
			//The input stream will point to the character after lastChar.
			//returns false if hit EOF. tokenToReturn will be set appropriately.
			bool walkPastWhiteSpace();

			///\return true if \param c is an identifier character (2nd letter or greater, the first can't be numeric)
			///An identifier character matches the regex [a-zA-z_0-9]
			bool isIdentifier(char c);

			Token lastNumericToken;

			Token* tokenToReturn;
	};

}
#endif /* SMTLIBOUTPUTLEXER_H_ */
