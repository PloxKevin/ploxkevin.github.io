// Multiplayer Host Game Logic
class MultiplayerHost {
    constructor() {
        this.gridSize = 7;
        this.classPos = {x: 0, y: 0};
        this.aiPos = {x: 0, y: 0};
        this.treasurePos = {x: 0, y: 0};
        this.round = 1;
        this.classWins = 0;
        this.aiWins = 0;
        this.gameActive = false;
        
        // Multiplayer
        this.peer = null;
        this.connections = new Map(); // playerId -> {connection, playerName, score}
        this.currentVotes = new Map(); // playerId -> direction
        this.roomCode = this.generateRoomCode();
        
        // AI
        this.qAgent = new QLearningAgent(this.gridSize);
        this.preTrainedQTables = {};
        
        // Voting
        this.voteTimer = null;
        this.voteTimeRemaining = 5;
        
        this.initElements();
        this.initPeer();
        this.initEventListeners();
        this.initPretrainedNetworks();
        this.render();
    }
    
    generateRoomCode() {
        const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
        let code = '';
        for (let i = 0; i < 4; i++) {
            code += chars[Math.floor(Math.random() * chars.length)];
        }
        return code;
    }
    
    initElements() {
        this.grid = document.getElementById('game-grid');
        this.roomCodeEl = document.getElementById('room-code');
        this.joinUrlEl = document.getElementById('join-url');
        this.studentCountEl = document.getElementById('student-count');
        this.studentListEl = document.getElementById('student-list');
        this.qrCanvas = document.getElementById('qr-code');
        
        this.classWinsEl = document.getElementById('class-wins');
        this.aiWinsEl = document.getElementById('ai-wins');
        this.currentRoundEl = document.getElementById('current-round');
        
        this.voteTimerEl = document.getElementById('vote-timer');
        this.voteDisplays = {
            up: { count: document.getElementById('vote-up'), fill: document.getElementById('vote-up-fill') },
            down: { count: document.getElementById('vote-down'), fill: document.getElementById('vote-down-fill') },
            left: { count: document.getElementById('vote-left'), fill: document.getElementById('vote-left-fill') },
            right: { count: document.getElementById('vote-right'), fill: document.getElementById('vote-right-fill') }
        };
        
        this.aiModeEl = document.getElementById('ai-mode');
        this.explorationEl = document.getElementById('exploration');
        this.lastActionEl = document.getElementById('last-action');
        this.rewardEl = document.getElementById('reward');
        
        this.qHeatmapCanvas = document.getElementById('q-heatmap');
        this.qCtx = this.qHeatmapCanvas.getContext('2d');
        
        this.leaderboardEl = document.getElementById('leaderboard');
        
        this.startBtn = document.getElementById('start-btn');
        this.nextRoundBtn = document.getElementById('next-round-btn');
        this.resetAiBtn = document.getElementById('reset-ai-btn');
        this.aiLevelSelect = document.getElementById('ai-level');
        
        // Display room code
        this.roomCodeEl.textContent = this.roomCode;
        document.getElementById('wait-code').textContent = this.roomCode;
        
        // Create join URL
        const baseUrl = window.location.origin + window.location.pathname.replace('host.html', 'student.html');
        this.joinUrlEl.textContent = baseUrl;
        
        // Generate QR code
        this.generateQRCode(baseUrl);
    }
    
    initPeer() {
        // Create peer with specific ID based on room code
        const peerId = 'treasurehunt-' + this.roomCode;
        this.peer = new Peer(peerId);
        
        this.peer.on('open', (id) => {
            console.log('Host peer ID:', id);
            this.showNotification('✅ Kamer klaar! Code: ' + this.roomCode);
        });
        
        this.peer.on('connection', (conn) => {
            this.handleNewConnection(conn);
        });
        
        this.peer.on('error', (err) => {
            console.error('Peer error:', err);
            if (err.type === 'unavailable-id') {
                // Generate new room code if ID is taken
                this.roomCode = this.generateRoomCode();
                this.initPeer();
            }
        });
    }
    
    handleNewConnection(conn) {
        conn.on('open', () => {
            console.log('New student connected');
        });
        
        conn.on('data', (data) => {
            this.handleStudentMessage(conn, data);
        });
        
        conn.on('close', () => {
            this.handleStudentDisconnect(conn);
        });
    }
    
    handleStudentMessage(conn, data) {
        switch(data.type) {
            case 'join':
                this.addStudent(conn, data.playerName, data.playerId);
                break;
            case 'vote':
                this.recordVote(data.playerName, data.direction);
                break;
        }
    }
    
    addStudent(conn, playerName, playerId) {
        // Store connection and player info
        this.connections.set(playerId, {
            connection: conn,
            playerName: playerName,
            score: 0,
            voted: false
        });
        
        // Send welcome message
        conn.send({
            type: 'welcome',
            playerName: playerName
        });
        
        // Update UI
        this.updateStudentDisplay();
        this.showNotification(`👋 ${playerName} heeft zich aangesloten!`);
    }
    
    handleStudentDisconnect(conn) {
        // Find and remove disconnected student
        for (const [playerId, playerData] of this.connections.entries()) {
            if (playerData.connection === conn) {
                this.showNotification(`👋 ${playerData.playerName} heeft verlaten`);
                this.connections.delete(playerId);
                this.updateStudentDisplay();
                break;
            }
        }
    }
    
    updateStudentDisplay() {
        this.studentCountEl.textContent = this.connections.size;
        
        if (this.connections.size === 0) {
            this.studentListEl.innerHTML = `
                <div style="text-align: center; color: #9ca3af; padding: 20px;">
                    Wacht op leerlingen...<br>
                    Laat ze naar student.html gaan<br>
                    en code <span style="font-weight: bold;">${this.roomCode}</span> invoeren
                </div>
            `;
            return;
        }
        
        this.studentListEl.innerHTML = '';
        for (const [playerId, playerData] of this.connections.entries()) {
            const card = document.createElement('div');
            card.className = 'student-card' + (playerData.voted ? ' voted' : '');
            card.innerHTML = `
                <span class="student-name">${playerData.playerName}</span>
                <div class="student-stats">
                    <span class="student-score">${playerData.score} pts</span>
                    ${playerData.voted ? '✅' : '⏳'}
                </div>
            `;
            this.studentListEl.appendChild(card);
        }
    }
    
    initEventListeners() {
        this.startBtn.addEventListener('click', () => this.startNewGame());
        this.nextRoundBtn.addEventListener('click', () => this.nextRound());
        this.resetAiBtn.addEventListener('click', () => this.resetAI());
        
        this.aiLevelSelect.addEventListener('change', (e) => {
            if (e.target.value !== 'live') {
                this.loadPretrainedNetwork(e.target.value);
            }
        });
    }
    
    initPretrainedNetworks() {
        // Generate pre-trained Q-tables
        this.generatePretrainedNetwork('beginner', 100);
        this.generatePretrainedNetwork('intermediate', 500);
        this.generatePretrainedNetwork('expert', 1000);
    }
    
    generatePretrainedNetwork(level, episodes) {
        const agent = new QLearningAgent(this.gridSize);
        
        for (let ep = 0; ep < episodes; ep++) {
            let state = '0,0';
            const treasureX = Math.floor(Math.random() * this.gridSize);
            const treasureY = Math.floor(Math.random() * this.gridSize);
            
            for (let step = 0; step < 50; step++) {
                const action = agent.selectAction(state);
                const [x, y] = state.split(',').map(Number);
                let newX = x, newY = y;
                
                switch(action) {
                    case 0: newY = Math.max(0, y - 1); break;
                    case 1: newY = Math.min(this.gridSize - 1, y + 1); break;
                    case 2: newX = Math.max(0, x - 1); break;
                    case 3: newX = Math.min(this.gridSize - 1, x + 1); break;
                }
                
                const oldDist = Math.abs(x - treasureX) + Math.abs(y - treasureY);
                const newDist = Math.abs(newX - treasureX) + Math.abs(newY - treasureY);
                let reward = (oldDist - newDist) * 10;
                
                if (newX === treasureX && newY === treasureY) {
                    reward = 100;
                }
                
                const nextState = `${newX},${newY}`;
                agent.update(state, action, reward, nextState);
                
                state = nextState;
                if (newX === treasureX && newY === treasureY) break;
            }
            
            agent.decayEpsilon();
        }
        
        this.preTrainedQTables[level] = { ...agent.qTable };
    }
    
    loadPretrainedNetwork(level) {
        this.qAgent.qTable = { ...this.preTrainedQTables[level] };
        this.qAgent.epsilon = 0.1;
        this.updateAIDisplay();
        this.aiModeEl.textContent = `Pre-trained ${level}`;
    }
    
    generateQRCode(url) {
        QRCode.toCanvas(this.qrCanvas, url, {
            width: 150,
            margin: 1,
            color: {
                dark: '#2563eb',
                light: '#ffffff'
            }
        });
    }
    
    broadcast(message) {
        for (const [playerId, playerData] of this.connections.entries()) {
            try {
                playerData.connection.send(message);
            } catch (err) {
                console.error('Error sending to', playerData.playerName, err);
            }
        }
    }
    
    startNewGame() {
        this.round = 1;
        this.classWins = 0;
        this.aiWins = 0;
        
        // Reset scores
        for (const [playerId, playerData] of this.connections.entries()) {
            playerData.score = 0;
        }
        
        this.updateDisplay();
        
        // Notify students
        this.broadcast({ type: 'gameStart' });
        
        this.startRound();
    }
    
    startRound() {
        this.gameActive = true;
        this.nextRoundBtn.disabled = true;
        
        // Reset positions
        this.classPos = {x: 0, y: 0};
        this.aiPos = {x: 0, y: 0};
        
        // Random treasure
        do {
            this.treasurePos = {
                x: Math.floor(Math.random() * this.gridSize),
                y: Math.floor(Math.random() * this.gridSize)
            };
        } while (this.treasurePos.x === 0 && this.treasurePos.y === 0);
        
        // Reset votes
        this.currentVotes.clear();
        for (const [playerId, playerData] of this.connections.entries()) {
            playerData.voted = false;
        }
        
        this.render();
        this.updateStudentDisplay();
        
        // Notify students
        this.broadcast({
            type: 'roundStart',
            round: this.round
        });
        
        // Show countdown
        this.showCountdown(3, () => {
            // Start with AI move
            this.makeAIMove();
        });
    }
    
    showCountdown(seconds, callback) {
        const overlay = document.getElementById('countdown-overlay');
        const number = document.getElementById('countdown-number');
        
        overlay.classList.add('show');
        
        let count = seconds;
        number.textContent = count;
        
        const interval = setInterval(() => {
            count--;
            if (count > 0) {
                number.textContent = count;
            } else {
                clearInterval(interval);
                overlay.classList.remove('show');
                callback();
            }
        }, 1000);
    }
    
    makeAIMove() {
        if (!this.gameActive) return;
        
        const state = `${this.aiPos.x},${this.aiPos.y}`;
        const action = this.qAgent.selectAction(state);
        
        const actions = ['Omhoog', 'Omlaag', 'Links', 'Rechts'];
        this.lastActionEl.textContent = actions[action];
        
        const oldPos = {...this.aiPos};
        
        switch(action) {
            case 0: this.aiPos.y = Math.max(0, this.aiPos.y - 1); break;
            case 1: this.aiPos.y = Math.min(this.gridSize - 1, this.aiPos.y + 1); break;
            case 2: this.aiPos.x = Math.max(0, this.aiPos.x - 1); break;
            case 3: this.aiPos.x = Math.min(this.gridSize - 1, this.aiPos.x + 1); break;
        }
        
        // Calculate reward
        const oldDist = this.getDistance(oldPos, this.treasurePos);
        const newDist = this.getDistance(this.aiPos, this.treasurePos);
        let reward = (oldDist - newDist) * 10;
        
        if (this.aiPos.x === this.treasurePos.x && this.aiPos.y === this.treasurePos.y) {
            reward = 100;
            this.endRound('ai');
            return;
        }
        
        this.rewardEl.textContent = reward > 0 ? `+${reward}` : reward;
        
        // Update Q-learning
        const nextState = `${this.aiPos.x},${this.aiPos.y}`;
        this.qAgent.update(state, action, reward, nextState);
        
        this.render();
        this.updateAIDisplay();
        
        // Start voting for class move
        if (this.gameActive) {
            this.startVoting();
        }
    }
    
    startVoting() {
        this.currentVotes.clear();
        this.voteTimeRemaining = 5;
        
        // Reset vote displays
        for (const dir in this.voteDisplays) {
            this.voteDisplays[dir].count.textContent = '0';
            this.voteDisplays[dir].fill.style.height = '0%';
        }
        
        // Reset student voted status
        for (const [playerId, playerData] of this.connections.entries()) {
            playerData.voted = false;
        }
        this.updateStudentDisplay();
        
        // Notify students to start voting
        this.broadcast({ type: 'votingStart' });
        
        // Start countdown
        this.voteTimer = setInterval(() => {
            this.voteTimeRemaining--;
            this.voteTimerEl.textContent = this.voteTimeRemaining;
            
            if (this.voteTimeRemaining <= 0) {
                clearInterval(this.voteTimer);
                this.processVotes();
            }
        }, 1000);
    }
    
    recordVote(playerName, direction) {
        // Find player
        let playerId = null;
        for (const [id, data] of this.connections.entries()) {
            if (data.playerName === playerName) {
                playerId = id;
                break;
            }
        }
        
        if (!playerId || this.connections.get(playerId).voted) return;
        
        // Record vote
        this.currentVotes.set(playerId, direction);
        this.connections.get(playerId).voted = true;
        
        // Update display
        this.updateVoteDisplay();
        this.updateStudentDisplay();
    }
    
    updateVoteDisplay() {
        const voteCounts = { up: 0, down: 0, left: 0, right: 0 };
        
        for (const direction of this.currentVotes.values()) {
            voteCounts[direction]++;
        }
        
        const maxVotes = Math.max(1, ...Object.values(voteCounts));
        
        for (const dir in voteCounts) {
            this.voteDisplays[dir].count.textContent = voteCounts[dir];
            const percentage = (voteCounts[dir] / maxVotes) * 100;
            this.voteDisplays[dir].fill.style.height = `${percentage}%`;
        }
    }
    
    processVotes() {
        // Notify students voting ended
        this.broadcast({ type: 'votingEnd' });
        
        // Count votes
        const voteCounts = { up: 0, down: 0, left: 0, right: 0 };
        
        for (const direction of this.currentVotes.values()) {
            voteCounts[direction]++;
        }
        
        // Find winning direction
        let winningDirection = 'up';
        let maxVotes = 0;
        
        for (const dir in voteCounts) {
            if (voteCounts[dir] > maxVotes) {
                maxVotes = voteCounts[dir];
                winningDirection = dir;
            }
        }
        
        // If no votes, random direction
        if (maxVotes === 0) {
            const dirs = ['up', 'down', 'left', 'right'];
            winningDirection = dirs[Math.floor(Math.random() * 4)];
        }
        
        this.makeClassMove(winningDirection);
    }
    
    makeClassMove(direction) {
        switch(direction) {
            case 'up': this.classPos.y = Math.max(0, this.classPos.y - 1); break;
            case 'down': this.classPos.y = Math.min(this.gridSize - 1, this.classPos.y + 1); break;
            case 'left': this.classPos.x = Math.max(0, this.classPos.x - 1); break;
            case 'right': this.classPos.x = Math.min(this.gridSize - 1, this.classPos.x + 1); break;
        }
        
        this.render();
        
        if (this.classPos.x === this.treasurePos.x && this.classPos.y === this.treasurePos.y) {
            // Get correct voters for scoring
            const correctVoters = [];
            for (const [playerId, voteDir] of this.currentVotes.entries()) {
                if (voteDir === direction) {
                    const player = this.connections.get(playerId);
                    correctVoters.push(player.playerName);
                    player.score += 10;
                }
            }
            
            this.endRound('class', correctVoters);
        } else {
            // Continue with AI move
            setTimeout(() => {
                if (this.gameActive) {
                    this.makeAIMove();
                }
            }, 1000);
        }
    }
    
    endRound(winner, correctVoters = []) {
        this.gameActive = false;
        clearInterval(this.voteTimer);
        
        if (winner === 'class') {
            this.classWins++;
        } else {
            this.aiWins++;
        }
        
        this.updateDisplay();
        this.updateLeaderboard();
        
        // Notify students
        this.broadcast({
            type: 'roundEnd',
            winner: winner,
            correctVoters: correctVoters
        });
        
        // Decay epsilon for AI learning
        this.qAgent.decayEpsilon();
        
        if (this.round < 10) {
            this.nextRoundBtn.disabled = false;
        } else {
            this.endGame();
        }
    }
    
    nextRound() {
        this.round++;
        this.updateDisplay();
        this.startRound();
    }
    
    endGame() {
        const winner = this.classWins > this.aiWins ? 'class' : 'ai';
        
        // Get top players
        const playerArray = Array.from(this.connections.values());
        playerArray.sort((a, b) => b.score - a.score);
        const topPlayers = playerArray.slice(0, 3).map(p => p.playerName);
        
        // Notify students
        this.broadcast({
            type: 'gameEnd',
            winner: winner,
            classWins: this.classWins,
            aiWins: this.aiWins,
            topPlayers: topPlayers
        });
        
        this.showNotification(`🏆 Spel afgelopen! ${winner === 'class' ? 'Klas' : 'AI'} wint!`);
    }
    
    resetAI() {
        this.qAgent = new QLearningAgent(this.gridSize);
        this.updateAIDisplay();
        this.aiModeEl.textContent = 'Live leren (gereset)';
    }
    
    getDistance(pos1, pos2) {
        return Math.abs(pos1.x - pos2.x) + Math.abs(pos1.y - pos2.y);
    }
    
    render() {
        this.grid.innerHTML = '';
        
        for (let y = 0; y < this.gridSize; y++) {
            for (let x = 0; x < this.gridSize; x++) {
                const cell = document.createElement('div');
                cell.className = 'cell';
                
                // Distance coloring
                const dist = this.getDistance({x, y}, this.treasurePos);
                if (dist <= 1) cell.classList.add('hot');
                else if (dist <= 2) cell.classList.add('warm');
                else if (dist >= 4) cell.classList.add('cold');
                
                // Entities
                if (x === this.classPos.x && y === this.classPos.y) {
                    cell.classList.add('player-class');
                    cell.textContent = '😊';
                }
                if (x === this.aiPos.x && y === this.aiPos.y) {
                    cell.classList.add('player-ai');
                    cell.textContent = '🤖';
                }
                if (x === this.treasurePos.x && y === this.treasurePos.y) {
                    cell.classList.add('treasure');
                    cell.textContent = '💎';
                }
                
                this.grid.appendChild(cell);
            }
        }
        
        // Update winning team highlight
        document.getElementById('class-score-card').classList.toggle('winning', this.classWins > this.aiWins);
        document.getElementById('ai-score-card').classList.toggle('winning', this.aiWins > this.classWins);
    }
    
    updateDisplay() {
        this.classWinsEl.textContent = this.classWins;
        this.aiWinsEl.textContent = this.aiWins;
        this.currentRoundEl.textContent = this.round;
    }
    
    updateAIDisplay() {
        const epsilon = this.qAgent.epsilon;
        this.explorationEl.textContent = `${Math.round(epsilon * 100)}%`;
        
        this.drawQHeatmap();
    }
    
    drawQHeatmap() {
        const cellSize = 250 / this.gridSize;
        this.qCtx.clearRect(0, 0, 250, 250);
        
        for (let y = 0; y < this.gridSize; y++) {
            for (let x = 0; x < this.gridSize; x++) {
                const state = `${x},${y}`;
                const qValues = this.qAgent.qTable[state] || [0, 0, 0, 0];
                const maxQ = Math.max(...qValues);
                
                const intensity = Math.min(255, Math.abs(maxQ) * 2.5);
                if (maxQ > 0) {
                    this.qCtx.fillStyle = `rgb(0, ${intensity}, 0)`;
                } else if (maxQ < 0) {
                    this.qCtx.fillStyle = `rgb(${intensity}, 0, 0)`;
                } else {
                    this.qCtx.fillStyle = 'rgb(200, 200, 200)';
                }
                
                this.qCtx.fillRect(x * cellSize, y * cellSize, cellSize - 1, cellSize - 1);
                
                // Mark treasure
                if (x === this.treasurePos.x && y === this.treasurePos.y) {
                    this.qCtx.fillStyle = 'gold';
                    this.qCtx.beginPath();
                    this.qCtx.arc(
                        x * cellSize + cellSize/2,
                        y * cellSize + cellSize/2,
                        cellSize/3,
                        0, 2 * Math.PI
                    );
                    this.qCtx.fill();
                }
            }
        }
    }
    
    updateLeaderboard() {
        const playerArray = Array.from(this.connections.values());
        playerArray.sort((a, b) => b.score - a.score);
        
        this.leaderboardEl.innerHTML = '';
        
        playerArray.slice(0, 5).forEach((player, index) => {
            const item = document.createElement('li');
            item.className = 'leaderboard-item';
            item.innerHTML = `
                <span>${index + 1}. ${player.playerName}</span>
                <span>${player.score} pts</span>
            `;
            this.leaderboardEl.appendChild(item);
        });
    }
    
    showNotification(message) {
        const notification = document.createElement('div');
        notification.className = 'notification';
        notification.textContent = message;
        document.body.appendChild(notification);
        
        setTimeout(() => notification.remove(), 3000);
    }
}

// Q-Learning Agent
class QLearningAgent {
    constructor(gridSize) {
        this.gridSize = gridSize;
        this.qTable = {};
        this.alpha = 0.1;
        this.gamma = 0.9;
        this.epsilon = 1.0;
        this.epsilonDecay = 0.9;
        this.minEpsilon = 0.1;
    }
    
    getQValues(state) {
        if (!this.qTable[state]) {
            this.qTable[state] = [0, 0, 0, 0];
        }
        return this.qTable[state];
    }
    
    selectAction(state) {
        if (Math.random() < this.epsilon) {
            return Math.floor(Math.random() * 4);
        } else {
            const qValues = this.getQValues(state);
            const maxQ = Math.max(...qValues);
            const bestActions = [];
            qValues.forEach((q, i) => {
                if (q === maxQ) bestActions.push(i);
            });
            return bestActions[Math.floor(Math.random() * bestActions.length)];
        }
    }
    
    update(state, action, reward, nextState) {
        const qValues = this.getQValues(state);
        const nextQValues = this.getQValues(nextState);
        const maxNextQ = Math.max(...nextQValues);
        
        qValues[action] = qValues[action] + this.alpha * (reward + this.gamma * maxNextQ - qValues[action]);
        
        this.qTable[state] = qValues;
    }
    
    decayEpsilon() {
        this.epsilon = Math.max(this.minEpsilon, this.epsilon * this.epsilonDecay);
    }
}

// Initialize on load
document.addEventListener('DOMContentLoaded', () => {
    new MultiplayerHost();
});