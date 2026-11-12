@echo off
cd /d "%~dp0"
echo Open the address shown below on your iPhone (same Wi-Fi)
echo.
python app.py --host 0.0.0.0 --no-browser
pause
