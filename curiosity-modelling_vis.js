// CS171 Curiosity Modelling - Dual Knights Endgame
// Jiahua Chen and Anirudh Narsipur
// Feb 22, 2021

// INSTRUCTIONS: Since this script loads external elements, "Execute" may need to be run twice
// to guarantee that visualization is showing properly.

// Setup for importing necessary scripts/plugins
function loadSources() {
  var styleSheet = document.createElement('link');
  styleSheet.setAttribute('rel','stylesheet');
  styleSheet.setAttribute('href','https://unpkg.com/@chrisoakman/chessboardjs@1.0.0/dist/chessboard-1.0.0.min.css');
  styleSheet.setAttribute('integrity','sha384-q94+BZtLrkL1/ohfjR8c6L+A6qzNH9R2hBLwyoAfu3i/WCvQjzL2RQJ3uNHDISdU');
  styleSheet.setAttribute('crossorigin','anonymous');
  document.head.appendChild(styleSheet);

  var jQueryImport = document.createElement('script');
  jQueryImport.setAttribute('src','https://code.jquery.com/jquery-3.5.1.min.js');
  jQueryImport.setAttribute('integrity','sha384-ZvpUoO/+PpLXR1lu4jmpXWu80pZlYUAfxl5NsBMWOEPSjUn/6Z/hRTt8+pR6L4N2');
  jQueryImport.setAttribute('crossorigin','anonymous');
  document.head.appendChild(jQueryImport);

  var chessboardImport = document.createElement('script');
  chessboardImport.setAttribute('src','https://unpkg.com/@chrisoakman/chessboardjs@1.0.0/dist/chessboard-1.0.0.min.js');
  chessboardImport.setAttribute('integrity','sha384-8Vi8VHwn3vjQ9eUHUxex3JSN/NFqUg3QbPyX8kWyb93+8AC/pPWTzj+nHtbC5bxD');
  chessboardImport.setAttribute('crossorigin','anonymous');
  document.head.appendChild(chessboardImport);
}

// Start of visualization code
const colors = {
  "White0": true,
  "Black0": false
}

const files = {
  "A0": 0,
  "B0": 1,
  "C0": 2,
  "D0": 3,
  "E0": 4,
  "F0": 5,
  "G0": 6,
  "H0": 7
}

const ranks = {
  "R10": 0,
  "R20": 1,
  "R30": 2,
  "R40": 3,
  "R50": 4,
  "R60": 5,
  "R70": 6,
  "R80": 7
}

var pieceColors = {};

function setColors() {
  clrs = clr.tuples()
  for (idx = 0; idx < clrs.length; idx++) {
    var piece = clrs[idx]._atoms;
    pieceColors[piece[0].toString()] = piece[1].toString();
  }
}

function getPieceNotation(colorString, pieceString) {
  if (pieceString.includes("King")) {
    return colors[colorString] ? "K" : "k";
  } else if (pieceString.includes("Knight")) {
    return colors[colorString] ? "N" : "n";
  } else if (pieceString.includes("Bishop")) {
    return colors[colorString] ? "B" : "b";
  } // Add more if model is extended to have more pieces!
}

function boardFENString(board) {
  const side = board.join(toMove).tuples()[0].toString();

  var boardArr = [];
  for (r = 0; r < 8; r++) {
    var thisRank = [];
    for (f = 0; f < 8; f++) {
      thisRank.push("1");
    }
    boardArr.push(thisRank);
  }

  const positions = board.join(places).tuples();
  for (idx = 0; idx < positions.length; idx++) {
    const posn = positions[idx];
    const thisFile = posn._atoms[0].toString();
    const thisRank = posn._atoms[1].toString();
    const thisPiece = posn._atoms[2].toString();
    const thisColor = pieceColors[thisPiece];

    boardArr[ranks[thisRank]][files[thisFile]] = getPieceNotation(thisColor, thisPiece);
  }

  var boardString = "";
  for (r = 7; r >= 0; r--) {
    for (f = 0; f < 8; f++) {
      boardString += boardArr[r][f];
    }
    boardString += "/";
  }
  console.log(boardString.slice(0, -1));
  return boardString.slice(0, -1);
}

function loadChessboard() {
  setColors();
  let board = Board
  while (next.join(board).tuples().length > 0) {
    board = next.join(board)
  }
  let i = 0;
  do {
    var config = {
      pieceTheme: 'https://chessboardjs.com/img/chesspieces/wikipedia/{piece}.png',
      position: boardFENString(board)
    }
    var chessboard = document.createElement('div');
    var boardName = 'board' + i;
    chessboard.setAttribute('id',boardName);
    chessboard.setAttribute('style','width: 300px; margin: 10px');
    div.appendChild(chessboard);
    var board1 = Chessboard(boardName, config)
    board = board.join(next);
    i++;
    console.log(i);
  } while (board.tuples()[0]);
}

div.innerHTML = '';
div.style.overflow = 'scroll';
if (!document.head.innerHTML.includes('chessboardjs@1.0.0')) {
  alert('Since this script loads external elements, "Execute" may need to be run twice or thrice (!!) to guarantee that visualization is showing properly.');
}
loadSources();
loadChessboard();
