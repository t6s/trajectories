import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

const gSize  = 40;

const renderer = new THREE.WebGLRenderer();
renderer.setSize(600, 600);
document.body.insertBefore(renderer.domElement, document.body.firstChild);

const camera = new THREE.PerspectiveCamera( 45, 1, 1, 500 );
camera.position.set(0, 1.5 * gSize, 0);
camera.lookAt( 0, 0, 0 );


let scene = new THREE.Scene();
scene.background = new THREE.Color( 'lightgrey' );

let grid = new THREE.GridHelper(gSize, gSize);
scene.add(grid);
grid.position.z = 0;
grid.position.y = 0.1;
grid.position.x = 0;

renderer.render( scene, camera );
var mouse = new THREE.Vector2();
var raycaster = new THREE.Raycaster();

const boardColor = new THREE.Color('lightpink');
const boardMat   = new THREE.MeshBasicMaterial({color: boardColor});
const boardGeometry = new THREE.BoxGeometry(gSize,0.1, gSize);
const boardCube = new THREE.Mesh(boardGeometry, boardMat);
boardCube.position.z = 0;
boardCube.position.y = 0;
boardCube.position.x = 0;
scene.add(boardCube);

var fromValid = false;
var fromX = 0;
var fromY = 0.2;
var fromZ = 0;
const fromColor = new THREE.Color('blue');
const fromMat   = new THREE.MeshBasicMaterial({color: fromColor});
// create the from Square
const fromGeometry = new THREE.BoxGeometry(0.9, 0.1, 0.9);
const fromCube = new THREE.Mesh(fromGeometry, fromMat);
// The initial position
fromCube.position.z = fromZ;
fromCube.position.y = -0.2;
fromCube.position.x = fromX;
scene.add(fromCube);

var toValid = false;
var fY = 0.2;
var tY = 0.2;
var toX = 0;
var toY = 0.2;
var toZ = 0;
var toColor = new THREE.Color('red');
const toMat   = new THREE.MeshBasicMaterial({color: toColor});
// create the to Square
const toGeometry = new THREE.BoxGeometry(0.9, 0.1, 0.9);
const toCube = new THREE.Mesh(toGeometry, toMat);
// The initial position
toCube.position.z = toZ;
toCube.position.y = -0.2;
toCube.position.x = toX;
scene.add(toCube);
renderer.render( scene, camera );

// set of borders on the screen
var  borders = [];
const cmaterial = new THREE.LineBasicMaterial( { color: 'brown' } );
var curves = [];

function addBorder(fX, fZ, tX, tZ) {
    if (tX < fX) {
        let xX = fX;
        let xZ = fZ;
        fX = tX;
        fZ = tZ;
        tX = xX;
        tZ = xZ;
    }
    console.log("addBorder " + fX + " " + fZ + " " + tX + " " + tZ);
    fromValid = false;  
    toValid = false;   
    fromCube.position.y = -0.2;
    toCube.position.y = -0.2;
    let test = false;
    let index = 0;
    let tline = null;
    borders.every(item => {
            if ((fX == item.fX) && (fZ == item.fZ) &&
                (tX == item.tX) && (tZ == item.tZ)) {
                test = true;
                tline = item.line;
                return false;
            };
            index++;
            return true;
    });
    if (test) {
        console.log("delete");
        scene.remove(tline);
        borders.splice(index, 1);
        renderer.render( scene, camera ); 
        return;
    }
    if (borders.length > 1) {
        console.log("full");
        fromValid = false;  
        toValid = false;   
        fromCube.position.y = -0.2;
        toCube.position.y = -0.2;
        renderer.render( scene, camera ); 
        return;
    }
    let fromVector = new THREE.Vector3(fX, fY, fZ ) ;
    let toVector = new THREE.Vector3(tX, tY, tZ ) ;
    let points = [fromVector, toVector];
    let geometry = new THREE.BufferGeometry().setFromPoints( points );
    let vline = new THREE.Line( geometry, borderMat );
    scene.add( vline );
    const v = {fX : fX, fZ : fZ, tX : tX, tZ : tZ, line : vline };
    borders.push(v);
    renderer.render( scene, camera ); 
}

// set of obstacles on the screen
var  obstacles = [];

function addObstacle(fX, fZ, tX, tZ) {
    if (tX < fX) {
        let xX = fX;
        let xZ = fZ;
        fX = tX;
        fZ = tZ;
        tX = xX;
        tZ = xZ;
    }
    console.log("addObstacle " + fX + " " + fZ + " " + tX + " " + tZ);
    fromValid = false;  
    toValid = false;   
    fromCube.position.y = -0.2;
    toCube.position.y = -0.2;
    let test = false;
    let index = 0;
    let tline = null;
    obstacles.every(item => {
            if ((fX == item.fX) && (fZ == item.fZ) &&
                (tX == item.tX) && (tZ == item.tZ)) {
                test = true;
                tline = item.line;
                return false;
            };
            index++;
            return true;
    });
    if (test) {
        console.log("delete");
        scene.remove(tline);
        obstacles.splice(index, 1);
        renderer.render( scene, camera ); 
        return;
    }
    let fromVector = new THREE.Vector3(fX, fY, fZ ) ;
    console.log(fromVector + "" + fX + " " + fY + " " + fZ);    
    let toVector = new THREE.Vector3(tX, tY, tZ ) ;
    console.log(toVector + "" + tX + " " + tY + " " + tZ);    
    let points = [fromVector, toVector];
    let geometry = new THREE.BufferGeometry().setFromPoints( points );
    let vline = new THREE.Line( geometry, lineMat );
    scene.add( vline );
    const v = {fX : fX, fZ : fZ, tX : tX, tZ : tZ, line : vline };
    obstacles.push(v);
    renderer.render( scene, camera ); 
}

var positions;
const lineColor = new THREE.Color( 'green' );
const lineMat = new THREE.LineBasicMaterial({color: lineColor, linewidth: 1});

const borderColor = new THREE.Color( 'black' );
const borderMat = new THREE.LineBasicMaterial({color: borderColor, linewidth: 1});

function onDocumentMouseDown( event ) {

    // Get screen-space x/y
    mouse.x = ( event.clientX / renderer.domElement.clientWidth ) * 2 - 1;
    mouse.y = - ( event.clientY / renderer.domElement.clientHeight ) * 2 + 1;

    // Perform raycast
    raycaster.setFromCamera( mouse, camera );

    // See if the ray from the camera into the world hits our mesh
    const intersects = raycaster.intersectObject( boardCube );

    // Check if an intersection took place
    if ( intersects.length == 0 ) {
        return;
    }
    let posX = intersects[0].point.x;
    let posZ = intersects[0].point.z;
    let dZ = Math.abs(Math.trunc(posZ) - posZ);
    let dX = Math.abs(Math.trunc(posX) - posX);
    if (((dZ < 0.1) || (0.9 < dZ)) || (dX < 0.1) || (0.9 < dX)) {
        return;
    }
    if (toValid && (modality == "positions")) {
        fromValid = false;
        toValid = false;
        fromCube.position.y = -0.2;
        toCube.position.y = -0.2;
        cleanCurves();
        renderer.render( scene, camera );  
    }
    if (fromValid) {
        toZ = Math.round(gSize + posZ + 0.5) -gSize - 0.5;
        toX = Math.round(gSize + posX + 0.5) -gSize - 0.5;
        if ((fromX == toX) && (fromZ != toZ)) {
            return;
        }
        console.log("modality = " + modality);
        if (modality == "borders") {
            fromValid = false;  
            toValid = true;         
            if ((fromX == toX) && (fromZ == toZ)) {
                fromCube.position.y = -0.2;
                toCube.position.y = -0.2;
                renderer.render( scene, camera ); 
                return;
            }
            cleanCurves();
            addBorder(fromX, fromZ, toX, toZ);
        }
        if (modality == "obstacles") {
            fromValid = false;  
            toValid = true;         
            if ((fromX == toX) && (fromZ == toZ)) {
                fromCube.position.y = -0.2;
                toCube.position.y = -0.2;
                renderer.render( scene, camera ); 
                return;
            }
            cleanCurves();
            addObstacle(fromX, fromZ, toX, toZ);
        }
        if (modality == "positions") {
            fromValid = true;         
            toValid = true;         
            toCube.position.z = toZ;
            toCube.position.y = toY;
            toCube.position.x = toX;
            renderer.render( scene, camera );
            positions = {fX : fromX, fZ : fromZ, tX : toX, tZ : toZ }
            cleanCurves();
            outState();
        }
    } else {
        fromValid = true;         
        fromZ = Math.round(gSize + posZ + 0.5) -gSize - 0.5;
        fromX = Math.round(gSize + posX + 0.5) -gSize - 0.5;
        fromCube.position.z = fromZ;
        fromCube.position.y = fromY;
        fromCube.position.x = fromX;
        toCube.position.y = -0.2;
        cleanCurves();
        renderer.render( scene, camera );
    }
}

renderer.domElement.addEventListener('click', onDocumentMouseDown, false);

const radioButtons = 
  document.querySelectorAll('input[name="modality"]');

for (const radioButton of radioButtons) {
    radioButton.addEventListener("click", setModality, false);
}

var modality = "";

function setModality() {
    cleanCurves();
    fromValid = false;  
    toValid = false;         
    fromCube.position.y = -0.2;
    toCube.position.y = -0.2;
    renderer.render( scene, camera );        
    for (const radioButton of radioButtons) {
        if (radioButton.checked) {
            modality = radioButton.value;
            console.log("new modality " + modality);
            break;
        }
    }
}
 
setModality();

function printVal (v) {
    let v1 = v + 0.5 + (gSize/2);
    let val = "";
    if (v1 < 10) {
        val += "0";
    }
    return val + v1 + "/" + gSize;
}

function printState() {
  let val = "Borders \n";
  for (const boarder of borders) {
    val += "from (" + printVal(boarder.fX) + ", " + printVal(boarder.fZ) + 
            ") -> (" + 
            printVal(boarder.tX) + ", " + printVal(boarder.tZ) + ")\n";  
  }
  val += "Obstables\n";
  for (const obstacle of obstacles) {
    val += "from (" + printVal(obstacle.fX) + ", " + printVal(obstacle.fZ)
            + ") -> (" + 
            printVal(obstacle.tX) + ", " + printVal(obstacle.tZ) + ")\n";  
  } 
  val += "Position\n";
  val += "Start (" + printVal(positions.fX) + ", " + printVal(positions.fZ) + ") To (" + 
            printVal(positions.tX) + ", " + printVal(positions.tZ) + ")\n";
  setTimeout(() => {  alert(val); }, 1000);  
}

function outVal (v) {
    let v1 = v + 0.5 + (gSize/2);
    let val = "+" + v1 + " " + "+" + gSize + " "
    return val;
}

console.log(curves.length);

function cleanCurves () {
    let i = 0; 
    console.log("curves " + curves);
    while (i < curves.length)
    for (const curve of curves) {
        scene.remove(curves[i]);
        i++;
    }
    renderer.render( scene, camera ); 
    curves = [];
}

function outState() {
  let val = "";
  val += outVal(positions.fX) + outVal(positions.fZ) + 
         outVal(positions.tX) + outVal(positions.tZ);
  if (borders.length != 2) {
    return;
  }
  if (borders[0].fZ <= borders[1].fZ) {
    val += outVal(borders[0].fX) + outVal(borders[0].fZ) + 
           outVal(borders[0].tX) + outVal(borders[0].tZ);  
    val += outVal(borders[1].fX) + outVal(borders[1].fZ) + 
           outVal(borders[1].tX) + outVal(borders[1].tZ);  
  } else {
    val += outVal(borders[1].fX) + outVal(borders[1].fZ) + 
           outVal(borders[1].tX) + outVal(borders[1].tZ);  
    val += outVal(borders[0].fX) + outVal(borders[0].fZ) + 
           outVal(borders[0].tX) + outVal(borders[0].tZ);  
  }
  for (const obstacle of obstacles) {
    val += outVal(obstacle.fX) + outVal(obstacle.fZ)
            + outVal(obstacle.tX) + outVal(obstacle.tZ);  
  } 
  console.log("boarders " + borders.length + " obstacles " + obstacles.length);
  console.log("val " + val);
  let res = smooth(val);
  console.log("res " + res);
  let res1 = res.split(' ').map(Number);
  let i = 0;
  while (i < res1.length) {
    if (res1[i] == 1) {
        /* Straight line */
        let fx = res1[i + 2] / res1 [i + 3] * gSize - 0.5 - gSize/2;
        let fy = 0.3;
        let fz = res1[i + 4] / res1 [i + 5] * gSize - 0.5 - gSize/2;
        let tx = res1[i + 6] / res1 [i + 7] * gSize - 0.5 - gSize/2;
        let ty = 0.3;
        let tz = res1[i + 8] / res1 [i + 9] * gSize - 0.5 - gSize/2;
        console.log("Adding a line" + fx + " " + fz + " " + tx + " " + tz);
        let epoints = [];
        epoints.push( new THREE.Vector3(fx, fy, fz) );
        epoints.push( new THREE.Vector3(tx, ty, tz));
        let egeometry = new THREE.BufferGeometry().setFromPoints( epoints );
        let sline = new THREE.Line( egeometry, cmaterial );
        curves.push(sline);
        scene.add( sline );
        renderer.render( scene, camera );
        i += 10;
    } else if (res1[i] == 2) {
        /* curve */
        let fx = res1[i + 2] / res1 [i + 3] * gSize - 0.5 - gSize/2;
        let fy = 0.3;
        let fz = res1[i + 4] / res1 [i + 5] * gSize - 0.5 - gSize/2;
        let cx = res1[i + 6] / res1 [i + 7] * gSize - 0.5 - gSize/2;
        let cy = 0.3;
        let cz = res1[i + 8] / res1 [i + 9] * gSize - 0.5 - gSize/2;
        let tx = res1[i + 10] / res1 [i + 11] * gSize - 0.5 - gSize/2;
        let ty = 0.3;
        let tz = res1[i + 12] / res1 [i + 13] * gSize - 0.5 - gSize/2;
        console.log("Adding a curve" + fx + " " + fz + " " 
                                     + cx + " " + cz + " " + tx + " " + tz);
        let ccurve = new THREE.QuadraticBezierCurve3(
                	new THREE.Vector3(fx, fy, fz ),
	                new THREE.Vector3(cx, cy, cz ),
	                new THREE.Vector3(tx, ty, tz )
                );
        let cpoints = ccurve.getPoints( 50 );
        let cgeometry = new THREE.BufferGeometry().setFromPoints( cpoints );
        let cline = new THREE.Line( cgeometry, cmaterial );
        scene.add( cline );
        curves.push(cline);
        i += 14;
    } else {
        i++;
    }
  }
}
